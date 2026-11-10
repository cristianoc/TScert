// The given statement-entry facts of the single pass (docs/drafts/single-pass.md,
// "4. Loop heads"), written once from the existing search's certificates:
// each case whose file name contains a pattern (every case with none) checked
// through the pipeline, its run kept, then `verifier --verify-units 6` over
// the same fragment and claims, its lines written to <dir>/<case file>.jsonl,
// each with its loop heads' facts the claims state (read by the claims-free
// pass, `--verify-units 8`).
//   node dev/single-pass-given.mts <dir> [pattern…]
import { spawnSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { cases, type Case } from "../pipeline/cases.mts";
import { pooled } from "../pipeline/run-cases.mts";
import { checkApart } from "../pipeline/verify-source.mts";
import { withoutEvidenceReuse } from "../pipeline/stages.mts";

const root = resolve(import.meta.dirname, "..");
const verifier = join(root, "lean/.lake/build/bin/verifier");
withoutEvidenceReuse();

/** The file key the pipeline's check of a run named: `--check-units`'s third argument. */
function fileKey(artifacts: string): string | null {
  const log = readFileSync(join(artifacts, "invocations.jsonl"), "utf8");
  const match = /"--check-units","fragment\.json","claims\.json","([^"]+)"/.exec(log);
  return match ? match[1] : null;
}

async function write(dir: string, test: Case): Promise<number> {
  const source = join(root, "pipeline/examples", `${test.file}.ts`);
  using outcome = await checkApart(source, test.project ? resolve(root, test.project) : undefined,
    test.typescriptErrors, undefined, true);
  const key = fileKey(outcome.artifacts);
  if (key === null) return 0;
  // The loop heads' facts too, the claims-free pass's (`TSCERT_GIVEN_FACTS`).
  const run = spawnSync(verifier, ["--verify-units", "6", join(outcome.artifacts, "fragment.json"),
    join(outcome.artifacts, "claims.json"), key, "12"], { encoding: "utf8", maxBuffer: 1 << 28,
    env: { ...process.env, TSCERT_GIVEN_FACTS: "1" } });
  const lines = run.stdout.split("\n").filter((l) => l.startsWith("{\"codes\""));
  const path = join(dir, `${test.file}.jsonl`);
  mkdirSync(dirname(path), { recursive: true });
  writeFileSync(path, lines.join("\n") + "\n");
  return lines.length;
}

const [dir, ...patterns] = process.argv.slice(2);
if (dir === undefined) {
  process.stderr.write("usage: node dev/single-pass-given.mts <dir> [pattern…]\n");
  process.exit(2);
}
mkdirSync(dir, { recursive: true });
const chosen = cases.filter((c) => patterns.length === 0 || patterns.some((p) => c.file.includes(p)));
const results = await pooled(chosen, (test) => write(dir, test));
const written = results.reduce((n, r) => n + (r.status === "fulfilled" ? r.value : 0), 0);
process.stdout.write(`${written} units' given facts written for ${chosen.length} cases\n`);
