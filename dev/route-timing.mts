// End-to-end time of one source file on each route, the parse included:
// `node pipeline/verify-source.mts <file> --project <dir>` run as a process
// of its own, its wall time and the units its outcome verifies.
//   node dev/route-timing.mts <pretext checkout> <work dir> [file…]
// For each file (by default src/prepare.ts and src/rich-inline.ts), in turn:
// the pipeline's route with evidence reuse off, cold (a fresh stage store
// under <work dir>) then warm (the same store again); the pipeline's route
// with evidence reuse on, warm over that store; the single-pass route
// (`TSCERT_ROUTE=single-pass`), cold (another fresh store) then warm. A fresh
// store also holds a fresh parse, so a cold run parses as the first check of
// a file does. The stores are removed at the end. Prints one line per run:
// the route, the store, the wall time, the outcome and the units verified of
// the units checked.
import { spawnSync } from "node:child_process";
import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";

const root = resolve(import.meta.dirname, "..");
const [pretextArgument, workArgument, ...chosen] = process.argv.slice(2);
if (pretextArgument === undefined || workArgument === undefined) {
  process.stderr.write("usage: node dev/route-timing.mts <pretext checkout> <work dir> [file…]\n");
  process.exit(2);
}
const pretext = resolve(pretextArgument), work = resolve(workArgument);
const files = chosen.length > 0 ? chosen : ["src/prepare.ts", "src/rich-inline.ts"];
mkdirSync(work, { recursive: true });
// The pretext project, as the performance gate states it (dev/perf-gate.mts).
const project = join(work, "pretext-project");
mkdirSync(project, { recursive: true });
writeFileSync(join(project, "tsconfig.json"), JSON.stringify({
  extends: join(pretext, "tsconfig.json"), compilerOptions: { types: [] },
  include: [join(pretext, "src/**/*.ts")], exclude: [join(pretext, "src/layout.test.ts")],
}, null, 2));

/** The units an outcome printed, and how many are verified. */
function counted(stdout: string): { status: string; verified: number; units: number; refused: string[] } {
  let value: unknown;
  try {
    value = JSON.parse(stdout);
  } catch {
    return { status: "no outcome", verified: 0, units: 0, refused: [] };
  }
  const field = (v: unknown, k: string): unknown => typeof v === "object" && v !== null && k in v ? Object.getOwnPropertyDescriptor(v, k)?.value : undefined;
  const status = field(value, "status");
  const units = field(value, "units");
  // The file's own units: a certified import's module run (`module:…`) is not one.
  const list: unknown[] = (Array.isArray(units) ? units : []).filter((u) => !String(field(u, "unit")).startsWith("module:"));
  const refused = list.filter((u) => field(u, "status") !== "verified").map((u) => String(field(u, "unit")));
  return { status: typeof status === "string" ? status : "no status", verified: list.length - refused.length, units: list.length, refused };
}

function run(file: string, route: string, store: string, reuse: boolean, label: string): void {
  const env: NodeJS.ProcessEnv = { ...process.env, TSCERT_STAGE_STORE: store, TSCERT_EVIDENCE_REUSE: reuse ? "1" : "0" };
  if (route === "single-pass") env.TSCERT_ROUTE = "single-pass";
  else delete env.TSCERT_ROUTE;
  const started = performance.now();
  const p = spawnSync("node", [join(root, "pipeline/verify-source.mts"), join(pretext, file), "--project", project],
    { encoding: "utf8", maxBuffer: 1 << 28, env, cwd: root });
  const seconds = (performance.now() - started) / 1000;
  const c = counted(p.stdout);
  process.stdout.write(`  ${label}  ${route}${route === "pipeline" ? ` reuse ${reuse ? "on" : "off"}` : ""}  ${seconds.toFixed(1)} s  ${c.status}  ${c.verified} of ${c.units} units verified` +
    `${c.refused.length > 0 ? `  refused: ${c.refused.join(" ")}` : ""}\n`);
}

for (const file of files) {
  const tag = file.replace(/[^A-Za-z0-9]+/g, "-");
  const pipelineStore = join(work, `store-pipeline-${tag}`), passStore = join(work, `store-pass-${tag}`);
  for (const s of [pipelineStore, passStore]) rmSync(s, { recursive: true, force: true });
  process.stdout.write(`${file}:\n`);
  run(file, "pipeline", pipelineStore, false, "cold");
  run(file, "pipeline", pipelineStore, false, "warm");
  run(file, "pipeline", pipelineStore, true, "warm");
  run(file, "single-pass", passStore, false, "cold");
  run(file, "single-pass", passStore, false, "warm");
  for (const s of [pipelineStore, passStore]) rmSync(s, { recursive: true, force: true });
}
