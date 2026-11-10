// The single forward pass (`verifier --verify-units 3`, docs/drafts/single-pass.md)
// against the pipeline on the pipeline cases: each case whose file name
// contains a pattern (every case with none) checked through the pipeline,
// its run kept, then the pass run over the same fragment and claims; each
// unit's two verdicts compared.
//   node dev/single-pass-agreement.mts [pattern…]
// With TSCERT_GIVEN_DIR set, each case's given statement-entry facts are read
// from <dir>/<case file>.jsonl (written by dev/single-pass-given.mts).
// With TSCERT_PASS_MODE=8, the pass runs over the fragment alone
// (`--verify-units 8`), its types computed by the verifier; with
// TSCERT_STANDINS_ALL set too, every function's and qualified import's
// footprint the case's claims state is supplied as a written-footprint
// stand-in (dev/single-pass-standins.mts).
// Prints the disagreements, then the counts: units agreeing, disagreeing,
// those the pass does not handle by construct, and those whose pipeline
// check did not finish (a stage's timeout), which decide nothing. Exits 0
// exactly when no unit disagrees, none is not handled and every case ran;
// a unit whose pipeline check did not finish is counted apart.
import { spawnSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { cases, type Case } from "../pipeline/cases.mts";
import { pooled } from "../pipeline/run-cases.mts";
import { checkApart } from "../pipeline/verify-source.mts";
import { withoutEvidenceReuse } from "../pipeline/stages.mts";
import { standIns } from "./single-pass-standins.mts";

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
  const mode = process.env.TSCERT_PASS_MODE ?? "3";
  let env: NodeJS.ProcessEnv = given === null ? process.env : { ...process.env, TSCERT_GIVEN: given };
  if (mode === "8" && process.env.TSCERT_STANDINS_ALL !== undefined) {
    const path = join(artifacts, "standins.json");
    writeFileSync(path, standIns(join(artifacts, "claims.json")) + "\n");
    env = { ...env, TSCERT_STANDINS: path };
  }
  // Mode 8 reads the fragment alone.
  const documents = mode === "8" ? [join(artifacts, "fragment.json")]
    : [join(artifacts, "fragment.json"), join(artifacts, "claims.json")];
  const run = spawnSync(verifier, ["--verify-units", mode, ...documents, key, "12"],
    { encoding: "utf8", maxBuffer: 1 << 28, env });
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
  // A file whose pipeline check did not finish (a stage's timeout) gives no
  // units: counted as one unfinished entry rather than dropped.
  if (units.length === 0) return outcome.status === "error"
    ? [{ file: test.file, unit: "(file)", pipeline: "unfinished", pass: "missing", agree: false, notHandled: null, why: "" }]
    : [];
  const key = fileKey(outcome.artifacts);
  if (key === null) return [];
  const givenDir = process.env.TSCERT_GIVEN_DIR;
  const pass = passVerdicts(outcome.artifacts, key, givenDir === undefined ? null : join(givenDir, `${test.file}.jsonl`));
  return units.map((u): Comparison => {
    const v = pass.get(u.unit);
    const notHandled = v ? construct(v.refusal) : null;
    const passSays = v === undefined ? "missing" : v.accepted ? "verified" : notHandled ? "not handled" : "refused";
    // A pipeline run that did not finish (a stage's timeout) decides nothing.
    const pipelineSays = u.status === "verified" ? "verified" : u.status === "error" ? "unfinished" : "refused";
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
  else if (!c.agree && c.pipeline !== "unfinished") process.stdout.write(`disagree: ${c.file} ${c.unit}: pipeline ${c.pipeline}, pass ${c.pass}: ${c.why}\n`);
}
const unfinished = all.filter((c) => c.pipeline === "unfinished").length;
const agree = all.filter((c) => c.agree).length;
const handled = all.filter((c) => c.notHandled === null && c.pipeline !== "unfinished");
process.stdout.write(`${all.length} units of ${chosen.length} cases: ${agree} agree, ` +
  `${handled.length - handled.filter((c) => c.agree).length} disagree, ${all.filter((c) => c.notHandled !== null).length} not handled, ` +
  `${unfinished} the pipeline did not finish\n`);
for (const [what, n] of [...constructs].sort((a, b) => b[1] - a[1])) process.stdout.write(`  not handled: ${what} ${n}\n`);
// The correctness half of the performance gate: every unit whose pipeline
// check finished agrees, none is not handled, and every case ran.
const failedCases = results.filter((r) => r.status === "rejected").length;
const disagreeing = handled.length - handled.filter((c) => c.agree).length;
const notHandled = all.filter((c) => c.notHandled !== null).length;
process.exitCode = disagreeing === 0 && notHandled === 0 && failedCases === 0 ? 0 : 1;
