// The types the verifier computes for a unit's expressions and statement
// entries (`verifier --verify-units 7`, lean/Verification/Source/Lowering/Synthesis.lean)
// against the types the claims document states, over the pipeline cases:
// each case whose file name contains a pattern (every case with none)
// checked through the pipeline, its run kept, then the comparison run over
// the same fragment and claims.
//   node dev/type-comparison.mts [--samples <file.jsonl>] [pattern…]
// Prints, per construct kind, how many occurrences are identical (the same
// meaning), wider, narrower, unrelated or undetermined; with `--samples`,
// writes each occurrence that is not identical, with its case, source text,
// both types and the reason, one per line.
import { spawnSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { cases, type Case } from "../pipeline/cases.mts";
import { pooled } from "../pipeline/run-cases.mts";
import { checkApart } from "../pipeline/verify-source.mts";
import { withoutEvidenceReuse } from "../pipeline/stages.mts";

const root = resolve(import.meta.dirname, "..");
const verifier = join(root, "lean/.lake/build/bin/verifier");
withoutEvidenceReuse();

const kinds = ["identifier", "literal", "comparison", "arithmetic", "member read", "call", "conditional", "other",
  "unvisited", "entry"];
const classes = ["identical", "wider", "narrower", "unrelated", "undetermined"];

type Count = { kind: string; class: string; n: number };
type Sample = { span?: [number, number]; pos?: number; name?: string; kind: string; class: string;
  computed: string; claimed: string };
type Result = { counts: Count[]; samples: (Sample & { file: string; text: string })[] };

/** The file key the pipeline's check of a run named: `--check-units`'s third argument. */
function fileKey(artifacts: string): string | null {
  const log = readFileSync(join(artifacts, "invocations.jsonl"), "utf8");
  const match = /"--check-units","fragment\.json","claims\.json","([^"]+)"/.exec(log);
  return match ? match[1] : null;
}

function isCount(v: unknown): v is Count {
  return typeof v === "object" && v !== null && "kind" in v && typeof v.kind === "string" &&
    "class" in v && typeof v.class === "string" && "n" in v && typeof v.n === "number";
}

function isSample(v: unknown): v is Sample {
  return typeof v === "object" && v !== null && "kind" in v && typeof v.kind === "string" &&
    "class" in v && typeof v.class === "string" && "computed" in v && typeof v.computed === "string" &&
    "claimed" in v && typeof v.claimed === "string";
}

async function compare(test: Case): Promise<Result> {
  const source = join(root, "pipeline/examples", `${test.file}.ts`);
  using outcome = await checkApart(source, test.project ? resolve(root, test.project) : undefined,
    test.typescriptErrors, undefined, true);
  const key = fileKey(outcome.artifacts);
  if (key === null) return { counts: [], samples: [] };
  const run = spawnSync(verifier, ["--verify-units", "7", join(outcome.artifacts, "fragment.json"),
    join(outcome.artifacts, "claims.json"), key, "12"], { encoding: "utf8", maxBuffer: 1 << 28 });
  const text = readFileSync(source, "utf8");
  const result: Result = { counts: [], samples: [] };
  for (const line of run.stdout.split("\n").filter((l) => l.startsWith("{"))) {
    const value: unknown = JSON.parse(line);
    if (typeof value !== "object" || value === null || !("comparison" in value)) continue;
    const comparison = value.comparison;
    if (typeof comparison !== "object" || comparison === null) continue;
    if ("counts" in comparison && Array.isArray(comparison.counts)) result.counts.push(...comparison.counts.filter(isCount));
    if ("samples" in comparison && Array.isArray(comparison.samples)) {
      for (const s of comparison.samples.filter(isSample)) {
        const at = s.span === undefined ? s.name ?? "" : text.slice(s.span[0], s.span[1]).replace(/\s+/g, " ").slice(0, 80);
        result.samples.push({ ...s, file: test.file, text: at });
      }
    }
  }
  return result;
}

const args = process.argv.slice(2);
const samplesAt = args[0] === "--samples" ? args[1] : undefined;
const patterns = samplesAt === undefined ? args : args.slice(2);
const chosen = cases.filter((c) => patterns.length === 0 || patterns.some((p) => c.file.includes(p)));
const results = await pooled(chosen, compare);
const table = new Map<string, Map<string, number>>();
const samples: Result["samples"] = [];
for (const [i, r] of results.entries()) {
  if (r.status !== "fulfilled") {
    process.stdout.write(`${chosen[i].file}: ${String(r.reason).slice(0, 200)}\n`);
    continue;
  }
  for (const c of r.value.counts) {
    const row = table.get(c.kind) ?? new Map<string, number>();
    row.set(c.class, (row.get(c.class) ?? 0) + c.n);
    table.set(c.kind, row);
  }
  samples.push(...r.value.samples);
}
process.stdout.write(`| kind | ${classes.join(" | ")} |\n|---|${classes.map(() => "---").join("|")}|\n`);
for (const kind of kinds) {
  const row = table.get(kind);
  if (row !== undefined) process.stdout.write(`| ${kind} | ${classes.map((c) => row.get(c) ?? 0).join(" | ")} |\n`);
}
if (samplesAt !== undefined) writeFileSync(samplesAt, samples.map((s) => JSON.stringify(s)).join("\n") + "\n");
