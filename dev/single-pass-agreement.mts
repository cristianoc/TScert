// The single forward pass (`verifier --verify-units 3`, docs/drafts/single-pass.md)
// against the pipeline on the pipeline cases: each case whose file name
// contains a pattern (every case with none) checked through the pipeline,
// its run kept, then the pass run over the same fragment and claims; each
// unit's two verdicts compared.
//   node dev/single-pass-agreement.mts [pattern…]
// With TSCERT_GIVEN_DIR set, each case's given statement-entry facts are read
// from <dir>/<case file>.jsonl (written by dev/single-pass-given.mts).
// Prints the disagreements, then the counts: units agreeing, disagreeing,
// and those the pass does not handle by construct.
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { cases, type Case } from "../pipeline/cases.mts";
import { pooled } from "../pipeline/run-cases.mts";
import { checkApart } from "../pipeline/verify-source.mts";
import { withoutEvidenceReuse } from "../pipeline/stages.mts";

const root = resolve(import.meta.dirname, "..");
const verifier = join(root, "lean/.lake/build/bin/verifier");
withoutEvidenceReuse();

type Verdict = { accepted: boolean; refusal: string };
type Comparison = { file: string; unit: string; pipeline: string; pass: string; agree: boolean; notHandled: string | null; why: string };

/** The file key the pipeline's check of a run named: `--check-units`'s third argument. */
function fileKey(artifacts: string): string | null {
  const log = readFileSync(join(artifacts, "invocations.jsonl"), "utf8");
  const match = /"--check-units","fragment\.json","claims\.json","([^"]+)"/.exec(log);
  return match ? match[1] : null;
}

/** The pass's verdict on each unit of a run's file. */
function passVerdicts(artifacts: string, key: string, given: string | null): Map<string, Verdict> {
  const env = given === null ? process.env : { ...process.env, TSCERT_GIVEN: given };
  const run = spawnSync(verifier, ["--verify-units", "3", join(artifacts, "fragment.json"),
    join(artifacts, "claims.json"), key, "12"], { encoding: "utf8", maxBuffer: 1 << 28, env });
  const verdicts = new Map<string, Verdict>();
  for (const line of run.stdout.split("\n").filter((l) => l.startsWith("{"))) {
    const value: unknown = JSON.parse(line);
    if (typeof value !== "object" || value === null) continue;
    const unit = "unit" in value ? value.unit : undefined;
    if (typeof unit !== "string") continue;
    const refusal = "refusal" in value && typeof value.refusal === "string" ? value.refusal : "";
    verdicts.set(unit, { accepted: "accepted" in value && value.accepted === true, refusal });
  }
  return verdicts;
}

/** The construct a refusal says the pass does not handle. */
function construct(refusal: string): string | null {
  const match = /not handled: ([^:(]*?)(?: at node \d+)?(?:[:(]|$)/.exec(refusal);
  return match ? match[1].trim() : null;
}

async function compare(test: Case): Promise<Comparison[]> {
  const source = join(root, "pipeline/examples", `${test.file}.ts`);
  using outcome = await checkApart(source, test.project ? resolve(root, test.project) : undefined,
    test.typescriptErrors, undefined, true);
  // A certified import's module run is checked apart (`--check-module`).
  const units = (outcome.units ?? []).filter((u) => !u.unit.startsWith("module:"));
  if (units.length === 0) return [];
  const key = fileKey(outcome.artifacts);
  if (key === null) return [];
  const givenDir = process.env.TSCERT_GIVEN_DIR;
  const pass = passVerdicts(outcome.artifacts, key, givenDir === undefined ? null : join(givenDir, `${test.file}.jsonl`));
  return units.map((u): Comparison => {
    const v = pass.get(u.unit);
    const notHandled = v ? construct(v.refusal) : null;
    const passSays = v === undefined ? "missing" : v.accepted ? "verified" : notHandled ? "not handled" : "refused";
    const pipelineSays = u.status === "verified" ? "verified" : "refused";
    return { file: test.file, unit: u.unit, pipeline: pipelineSays, pass: passSays,
      agree: passSays === pipelineSays, notHandled, why: v ? v.refusal.replace(/\s+/g, " ").slice(0, 160) : "" };
  });
}

const patterns = process.argv.slice(2);
const chosen = cases.filter((c) => patterns.length === 0 || patterns.some((p) => c.file.includes(p)));
const results = await pooled(chosen, compare);
const all: Comparison[] = [];
for (const [i, r] of results.entries()) {
  if (r.status === "fulfilled") all.push(...r.value);
  else process.stdout.write(`${chosen[i].file}: ${String(r.reason).slice(0, 200)}\n`);
}
const constructs = new Map<string, number>();
for (const c of all) {
  const what = c.notHandled?.replace(/ at node \d+$/, "") ?? null;
  if (what !== null) constructs.set(what, (constructs.get(what) ?? 0) + 1);
  else if (!c.agree) process.stdout.write(`disagree: ${c.file} ${c.unit}: pipeline ${c.pipeline}, pass ${c.pass}: ${c.why}\n`);
}
const agree = all.filter((c) => c.agree).length;
const handled = all.filter((c) => c.notHandled === null);
process.stdout.write(`${all.length} units of ${chosen.length} cases: ${agree} agree, ` +
  `${handled.length - handled.filter((c) => c.agree).length} disagree, ${all.length - handled.length} not handled\n`);
for (const [what, n] of [...constructs].sort((a, b) => b[1] - a[1])) process.stdout.write(`  not handled: ${what} ${n}\n`);
