// The single pass's performance gate (docs/drafts/single-pass.md, "The
// performance gate"): a fixed set of units, each captured through the
// single-pass route (its fragment kept), then the pass (`verifier
// --verify-interface-stage 8`, over the fragment alone, nothing supplied)
// run over it with its counts (`TSCERT_COUNTS`), compared with
// dev/perf-baseline.json.
//   node dev/perf-gate.mts <pretext checkout at ba09794f> [--update | --add]
// `--add` writes the baseline of the units it lacks, keeping the others'.
// A regression is a verdict other than the baseline's, a counter above its
// baseline, a unit whose visited nodes differ from its reached nodes, or the
// pass's CPU time (user and system of the verifier process, best of 3) above
// its baseline by more than the baseline's tolerance (a fraction of the
// baseline, at least its slack in milliseconds). Prints one table and
// each regression; exits 1 on any. `--update` writes the measured values as
// the baseline instead.
import { spawnSync } from "node:child_process";
import { copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { cases } from "../pipeline/cases.mts";
import { checkApart, sourceKey } from "../pipeline/verify-source.mts";
import { verifyWithInterfaces } from "../pipeline/module-interfaces.mts";

const root = resolve(import.meta.dirname, "..");
const verifier = join(root, "lean/.lake/build/bin/verifier");
const baselinePath = join(root, "dev/perf-baseline.json");

/** A unit of the gate: a function of a pretext file or of a pipeline case. */
type GateUnit = { name: string; unit: string } & ({ pretext: string } | { case: string });
const units: GateUnit[] = [
  { name: "pretext measureAnalysis", pretext: "prepare.ts", unit: "measureAnalysis" },
  { name: "pretext prepareRichInline", pretext: "rich-inline.ts", unit: "prepareRichInline" },
  { name: "pretext buildEngineProfile", pretext: "measurement.ts", unit: "buildEngineProfile" },
  { name: "loop with bounds", case: "pretext-clause-locals", unit: "scan" },
  { name: "loop over a parent chain", case: "blocker-compiler-api-grandparent-loop", unit: "use" },
  { name: "call in a loop", case: "blocker-pretext-loop-cell-call-result", unit: "extraSpacings" },
  { name: "union narrowing", case: "field-equality-union", unit: "kindOf" },
  { name: "logical narrowing", case: "logical-narrowing-past-reads", unit: "digits" },
  { name: "class", case: "class-values", unit: "fresh" },
  { name: "promise", case: "promise-then", unit: "show" },
  { name: "async", case: "async-await", unit: "chained" },
  { name: "handler", case: "try-catch", unit: "handled" },
  { name: "exceptional footprint", case: "exceptional-footprint-handler", unit: "largest" },
];

/** The counters the gate compares, by the name the pass prints them. */
const gated = ["nodes", "edges", "reached", "visited", "rules", "wholeStoreRules", "queries", "queryFacts",
  "merges", "mergeDiffs", "stateFactsSum", "stateFactsMax", "headsWritten", "headsFromClaims", "headsSupplied",
  "bytesRead"] as const;
type Counter = (typeof gated)[number];
type Counters = Record<Counter, number>;
type Measured = { verdict: string; refusal: string; cpuMs: number; wallMs: number; counters: Counters };
type Baseline = { tolerance: number; slackMs: number; units: Record<string, { verdict: string; cpuMs: number; counters: Counters }> };

/** A JSON object's numeric field, or 0. */
function numberField(value: unknown, key: string): number {
  if (typeof value !== "object" || value === null || !(key in value)) return 0;
  const v: unknown = Object.entries(value).find(([k]) => k === key)?.[1];
  return typeof v === "number" ? v : 0;
}

/** The baseline file, read field by field; null where there is none. */
function readBaseline(): Baseline | null {
  let text: string;
  try {
    text = readFileSync(baselinePath, "utf8");
  } catch {
    return null;
  }
  const value: unknown = JSON.parse(text);
  if (typeof value !== "object" || value === null || !("units" in value) || !("tolerance" in value)) return null;
  const tolerance = typeof value.tolerance === "number" ? value.tolerance : 0.3;
  const slackMs = "slackMs" in value && typeof value.slackMs === "number" ? value.slackMs : 20;
  const out: Baseline = { tolerance, slackMs, units: {} };
  if (typeof value.units !== "object" || value.units === null) return out;
  for (const [name, u] of Object.entries(value.units)) {
    if (typeof u !== "object" || u === null) continue;
    const verdict = "verdict" in u && typeof u.verdict === "string" ? u.verdict : "";
    const counters = "counters" in u ? u.counters : {};
    out.units[name] = { verdict, cpuMs: numberField(u, "cpuMs"),
      counters: Object.fromEntries(gated.map((k) => [k, numberField(counters, k)])) as Counters }; // asserted: one entry per gated counter
  }
  return out;
}

/** A unit's fragment and file key, captured through the single-pass route. */
async function capture(u: GateUnit, pretextRoot: string, work: string): Promise<{ dir: string; key: string }> {
  let source: string;
  let project: string | undefined;
  let typescriptErrors = false;
  if ("pretext" in u) {
    source = join(pretextRoot, "src", u.pretext);
    project = join(work, "pretext-project");
  } else {
    const c = cases.find((x) => x.file === u.case);
    if (c === undefined) throw Error(`no case ${u.case}`);
    source = join(root, "pipeline/examples", `${c.file}.ts`);
    project = c.project ? resolve(root, c.project) : undefined;
    typescriptErrors = c.typescriptErrors ?? false;
  }
  using outcome = await checkApart(source, project, typescriptErrors, undefined, true, { omitted: [], select: [u.unit] });
  const dir = join(work, u.name.replace(/[^A-Za-z0-9]+/g, "-"));
  mkdirSync(dir, { recursive: true });
  copyFileSync(join(outcome.artifacts, "fragment.json"), join(dir, "fragment.json"));
  return { dir, key: sourceKey(outcome.artifacts) };
}

/** The verifier run over a captured unit, its CPU time read by the shell
 * (`times`: the children's user and system time, its last line). */
function verify(dir: string, key: string, unit: string, env: NodeJS.ProcessEnv):
    { stdout: string; stderr: string; cpuMs: number; wallMs: number } {
  // Warm importer measurements exclude component preparation; the stage
  // records retain cold component CPU and wall time separately.
  const interfaces = verifyWithInterfaces(join(dir, "fragment.json"), key, unit, {
    mode: 8, fuel: 12, rounds: 4096, force: (env.TSCERT_FORCE ?? "").split(",").filter(Boolean), work: join(dir, "interfaces"), invocation: { limitMs: 60_000, force: false, recorder: null },
  }).interfaces;
  const started = performance.now();
  const args = ["--verify-interface-stage", "8", join(dir, "fragment.json"), interfaces.path, key, "12", unit];
  const run = spawnSync("/bin/sh", ["-c", '"$@"; status=$?; times >&2; exit $status', "sh", verifier, ...args],
    { encoding: "utf8", maxBuffer: 1 << 28, env });
  const wallMs = performance.now() - started;
  const last = run.stderr.trimEnd().split("\n").at(-1) ?? "";
  const seconds = [...last.matchAll(/(\d+)m([\d.]+)s/g)].map((m) => Number(m[1]) * 60 + Number(m[2]));
  if (seconds.length !== 2) throw Error(`no CPU time read from ${JSON.stringify(last)}`);
  return { stdout: run.stdout, stderr: run.stderr, cpuMs: (seconds[0] + seconds[1]) * 1000, wallMs };
}

/** The pass over a captured unit, three times: its verdict, counters and best CPU time. */
function measure(u: GateUnit, dir: string, key: string): Measured {
  const env = { ...process.env, TSCERT_COUNTS: "1" };
  const runs = [0, 1, 2].map(() => verify(dir, key, u.unit, env));
  const first = runs[0];
  let verdict = "missing", refusal = "";
  for (const line of first.stdout.split("\n").filter((l) => l.startsWith("{"))) {
    const v: unknown = JSON.parse(line);
    if (typeof v !== "object" || v === null) continue;
    // The unit's own line, not a module unit's (`module:<location>#<unit>`).
    if (!("unit" in v) || typeof v.unit !== "string" || !v.unit.startsWith(`${u.unit}@`)) continue;
    if ("accepted" in v && v.accepted === true) verdict = "verified";
    else if ("refusal" in v && typeof v.refusal === "string") {
      refusal = v.refusal.replace(/\s+/g, " ").slice(0, 160);
      verdict = /not handled/.test(v.refusal) ? "not handled" : "refused";
    }
  }
  const counters = Object.fromEntries(gated.map((k) => [k, 0])) as Counters; // asserted: one entry per gated counter
  for (const line of first.stderr.split("\n")) {
    const counts = /^counts: \S+ (\{.*\})$/.exec(line);
    if (counts) {
      const v: unknown = JSON.parse(counts[1]);
      for (const k of gated) counters[k] += numberField(v, k);
    }
    const read = /^counts-read: (\{.*\})$/.exec(line);
    if (read) {
      const v: unknown = JSON.parse(read[1]);
      counters.bytesRead = numberField(v, "fragmentBytes") + numberField(v, "interfaceBytes");
    }
  }
  const best = runs.reduce((a, b) => (b.cpuMs < a.cpuMs ? b : a));
  return { verdict, refusal, cpuMs: Math.round(best.cpuMs), wallMs: Math.round(best.wallMs), counters };
}

const args = process.argv.slice(2);
const add = args.includes("--add");
const update = args.includes("--update") || add;
const pretextRoot = args.find((a) => !a.startsWith("--"));
if (pretextRoot === undefined) {
  process.stderr.write("usage: node dev/perf-gate.mts <pretext checkout at ba09794f> [--update | --add]\n");
  process.exit(2);
}
const started = performance.now();
const work = mkdtempSync(join(tmpdir(), "perf-gate-"));
try {
  const pretext = resolve(pretextRoot);
  const head = spawnSync("git", ["-C", pretext, "rev-parse", "HEAD"], { encoding: "utf8" }).stdout.trim();
  if (!head.startsWith("ba09794f")) throw Error(`the pretext checkout is at ${head || "no commit"}, not ba09794f`);
  mkdirSync(join(work, "pretext-project"));
  writeFileSync(join(work, "pretext-project/tsconfig.json"), JSON.stringify({
    extends: join(pretext, "tsconfig.json"), compilerOptions: { types: [] },
    include: [join(pretext, "src/**/*.ts")], exclude: [join(pretext, "src/layout.test.ts")],
  }, null, 2));
  // Captured concurrently; measured one at a time.
  const captured = await Promise.all(units.map((u) => capture(u, pretext, work)));
  const captureMs = performance.now() - started;
  const measured = new Map<string, Measured>();
  for (const [i, u] of units.entries()) measured.set(u.name, measure(u, captured[i].dir, captured[i].key));
  const baseline = readBaseline();
  const tolerance = baseline?.tolerance ?? 0.3;
  const slackMs = baseline?.slackMs ?? 20;
  const regressions: string[] = [];
  const header = ["unit", "verdict", "cpu ms", ...gated, "wall ms"];
  const rows: string[][] = [header];
  for (const u of units) {
    const m = measured.get(u.name);
    if (m === undefined) continue;
    const b = baseline?.units[u.name];
    const with_ = (v: number | string, w: number | string | undefined): string => (w === undefined ? `${v}` : `${v}/${w}`);
    rows.push([u.name, with_(m.verdict, b?.verdict), with_(m.cpuMs, b?.cpuMs),
      ...gated.map((k) => with_(m.counters[k], b?.counters[k])), `${m.wallMs}`]);
    if (m.counters.visited !== m.counters.reached)
      regressions.push(`${u.name}: visited ${m.counters.visited} nodes of ${m.counters.reached} reached`);
    if (b === undefined) {
      if (!update) regressions.push(`${u.name}: no baseline`);
      continue;
    }
    if (m.verdict !== b.verdict) regressions.push(`${u.name}: verdict ${m.verdict}, baseline ${b.verdict} ${m.refusal}`);
    for (const k of gated) if (m.counters[k] > b.counters[k])
      regressions.push(`${u.name}: ${k} ${m.counters[k]} above its baseline ${b.counters[k]}`);
    if (m.cpuMs > Math.max(b.cpuMs * (1 + tolerance), b.cpuMs + slackMs))
      regressions.push(`${u.name}: CPU ${m.cpuMs} ms above its baseline ${b.cpuMs} ms by more than ${Math.round(tolerance * 100)}% and ${slackMs} ms`);
  }
  const widths = header.map((_, j) => Math.max(...rows.map((r) => r[j].length)));
  for (const r of rows) process.stdout.write(r.map((c, j) => c.padEnd(widths[j])).join("  ").trimEnd() + "\n");
  process.stdout.write(`measured value/baseline; CPU of the verifier process, best of 3; tolerance ${Math.round(tolerance * 100)}% or ${slackMs} ms; ` +
    `capture ${(captureMs / 1000).toFixed(1)} s, total ${((performance.now() - started) / 1000).toFixed(1)} s\n`);
  if (update) {
    const out: Baseline = { tolerance, slackMs, units: add ? { ...baseline?.units } : {} };
    for (const u of units) {
      const m = measured.get(u.name);
      if (m !== undefined && !(add && out.units[u.name] !== undefined))
        out.units[u.name] = { verdict: m.verdict, cpuMs: m.cpuMs, counters: m.counters };
    }
    writeFileSync(baselinePath, JSON.stringify(out, null, 2) + "\n");
    process.stdout.write(`baseline written: ${baselinePath}\n`);
  }
  for (const r of regressions) process.stdout.write(`regression: ${r}\n`);
  process.exitCode = regressions.length === 0 || update ? 0 : 1;
} finally {
  rmSync(work, { recursive: true, force: true });
}
