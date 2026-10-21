// The observed stages' tests (DESIGN.md, "Observed stages"): a parse
// replays after an unchanged run, and a change to an imported module, to a
// declaration file reached through node_modules, to the tsconfig, to the
// family descriptions or to the TypeScript package, and a module added where
// it changes resolution, each make it execute; forged entries are refused;
// TypeScript's diagnostics replay by the same mechanism. The confined
// compiler is killed on a read the API's queries do not serve, and the stages'
// code reads the file system only through tools/files.mts. Each run is a
// fresh process, as each pipeline run is; no build is needed.
import assert from "node:assert/strict";
import { spawnSync, type SpawnSyncReturns } from "node:child_process";
import { chmodSync, cpSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { runDirectory } from "../pipeline/run-directory.mts";
import { Recorder, codeIdentity, sha256, type Canonical } from "../pipeline/stages.mts";
import { Store } from "../pipeline/stage-store.mts";
import { parseSource, typeScriptErrors } from "../pipeline/verify-source.mts";
import { compilerApiFamily } from "../tools/compiler-api.mts";
import { launcherForTests, openCompiler, useInstallationForTests } from "../tools/compiler-channel.mts";
import { useFamiliesForTests } from "../tools/family-activation.mts";

const here = import.meta.dirname;
const repository = resolve(here, "..");

// A run of one observed stage in this process, printed as its attempt.
if (process.argv[2] === "--run") {
  const [stage, source, project, families, installation] = process.argv.slice(3);
  if (families === "changed")
    useFamiliesForTests([{ ...compilerApiFamily, corrections: compilerApiFamily.corrections.slice(1) }]);
  if (installation !== "-") useInstallationForTests(installation);
  const recorder = new Recorder(null);
  if (stage === "diagnostics") typeScriptErrors(recorder, source, project);
  else parseSource(source, project, runDirectory("observed-"), recorder);
  const record = recorder.records.find((r) => r.stage === stage);
  process.stdout.write(JSON.stringify({ execution: record?.execution, ineligible: record?.ineligible, key: record?.key }));
  process.exit(0);
}

const dir = runDirectory("tscert-observed-");
const root = join(dir, "store");
const store = new Store(root);
const fixture = join(dir, "project");
const write = (path: string, text: string): void => {
  mkdirSync(dirname(join(fixture, path)), { recursive: true });
  writeFileSync(join(fixture, path), text);
};
write("tsconfig.json", JSON.stringify({ compilerOptions: { strict: true, noEmit: true, target: "es2022", module: "preserve",
  moduleResolution: "bundler" }, files: ["main.ts"] }));
write("main.ts", [
  'import { dep } from "./dep";',
  'import { lib } from "pkg";',
  'import { m } from "./mod";',
  "export function f(x: number): number {",
  "  return dep(x) + lib(x) + m(x);",
  "}",
  "",
].join("\n"));
write("dep.ts", "export function dep(x: number): number {\n  return x;\n}\n");
write("node_modules/pkg/package.json", JSON.stringify({ name: "pkg", version: "1.0.0", types: "index.d.ts" }));
write("node_modules/pkg/index.d.ts", "export declare function lib(x: number): number;\n");
write("mod/index.ts", "export function m(x: number): number {\n  return x;\n}\n");
const main = join(fixture, "main.ts"), project = join(fixture, "tsconfig.json");

type Attempt = { execution: string; ineligible: string | null; key: string | null };
/** One stage in a fresh process. */
function run(stage: "parse" | "diagnostics" = "parse", families: string = "reviewed", installation: string = "-"): Attempt {
  const p = spawnSync(process.execPath, [import.meta.filename, "--run", stage, main, project, families, installation],
    { encoding: "utf8", env: { ...process.env, TSCERT_STAGE_STORE: root } });
  assert.equal(p.status, 0, p.stderr);
  const parsed: unknown = JSON.parse(p.stdout);
  if (typeof parsed !== "object" || parsed === null || !("execution" in parsed) || typeof parsed.execution !== "string")
    throw Error(`no attempt: ${p.stdout}`);
  const ineligible = "ineligible" in parsed && typeof parsed.ineligible === "string" ? parsed.ineligible : null;
  const key = "key" in parsed && typeof parsed.key === "string" ? parsed.key : null;
  return { execution: parsed.execution, ineligible, key };
}
/** The stage executes, publishing an entry, then replays it. */
function executesThenReplays(what: string, stage: "parse" | "diagnostics" = "parse", families: string = "reviewed",
    installation: string = "-"): string {
  const first = run(stage, families, installation);
  assert.equal(first.execution, "executed", `${what}: ${JSON.stringify(first)}`);
  assert.equal(first.ineligible, null, `${what}: ${JSON.stringify(first)}`);
  const second = run(stage, families, installation);
  assert.equal(second.execution, "replayed", `${what}, unchanged: ${JSON.stringify(second)}`);
  assert.equal(second.key, first.key);
  return second.key ?? "";
}

// --- a parse replays after an unchanged run; each change makes it execute
executesThenReplays("a first parse");
write("dep.ts", "export function dep(x: number): number {\n  return x + 1;\n}\n");
executesThenReplays("an imported module changed");
write("node_modules/pkg/index.d.ts", "export declare function lib(x: number): number;\nexport declare const other: string;\n");
executesThenReplays("a declaration file reached through node_modules changed");
write("tsconfig.json", JSON.stringify({ compilerOptions: { strict: true, noEmit: true, target: "es2023", module: "preserve",
  moduleResolution: "bundler" }, files: ["main.ts"] }));
executesThenReplays("the tsconfig changed");
// `./mod` resolved to `mod/index.ts`; a `mod.ts` beside it is found first.
write("mod.ts", "export function m(x: number): number {\n  return 2 * x;\n}\n");
executesThenReplays("a module added where it changes resolution");
executesThenReplays("the family descriptions changed", "parse", "changed");
const reviewed = run();
assert.equal(reviewed.execution, "replayed", "the reviewed descriptions again");

// --- the TypeScript package: a clone of the installation, then changed
const installation = join(dir, "installation");
for (const name of ["typescript", "@typescript"])
  cpSync(join(repository, "tools", "node_modules", name), join(installation, "node_modules", name), { recursive: true });
executesThenReplays("another TypeScript installation", "parse", "reviewed", installation);
const manifest = join(installation, "node_modules", "typescript", "package.json");
chmodSync(manifest, 0o644);
writeFileSync(manifest, readFileSync(manifest, "utf8") + "\n");
executesThenReplays("the TypeScript package changed", "parse", "reviewed", installation);

// --- forged entries are refused
const replayedKey = run().key ?? "";
const preKeys = readdirSync(join(root, "observed", "parse"));
const preKey = preKeys.find((p) => readdirSync(join(root, "observed", "parse", p)).includes(replayedKey)) ?? "";
assert.ok(preKey, "the replayed entry is referenced under its pre-key");
const references = join(root, "observed", "parse", preKey);
const entry = (key: string): string => join(root, "entries", "parse", key);
const found = store.finished("parse", replayedKey, null);
assert.ok(found);
// An entry whose observations answer otherwise now, the only one referenced.
const input: unknown = JSON.parse(found.result.input);
const observations = typeof input === "object" && input !== null && "observations" in input &&
  Array.isArray(input.observations) ? input.observations : [];
const forgedObservations: Canonical[] = observations.map((o: unknown) =>
  Array.isArray(o) && o[0] === "read" && o[1] === join(fixture, "dep.ts") ? ["read", o[1], "0".repeat(64)] : (o as Canonical)); // asserted: the observations of the entry this test's run just published
const forgedInput = JSON.stringify({ ...(input as object), observations: forgedObservations }); // asserted: the manifest object just parsed
assert.notEqual(forgedInput, found.result.input, "the forged entry differs");
const forgedKey = sha256(forgedInput);
store.publishFinished("parse", forgedKey, { ...found.result, input: forgedInput });
store.reference("parse", preKey, forgedKey);
rmSync(join(references, replayedKey));
assert.equal(run().execution, "executed", "an entry whose observations do not hold");
// A reference to an entry of another pre-key: its manifest is not this one's.
const other = readdirSync(join(root, "observed", "parse")).find((p) => p !== preKey) ?? "";
const otherKey = readdirSync(join(root, "observed", "parse", other))[0] ?? "";
for (const k of readdirSync(references)) rmSync(join(references, k));
store.reference("parse", preKey, otherKey);
assert.equal(run().execution, "executed", "a reference to another pre-key's entry");
// A stored result altered after publication.
for (const k of readdirSync(references)) rmSync(join(references, k));
store.reference("parse", preKey, replayedKey);
assert.equal(run().execution, "replayed", "the valid entry again");
const stdout = join(entry(replayedKey), "stdout");
chmodSync(entry(replayedKey), 0o755);
chmodSync(stdout, 0o644);
writeFileSync(stdout, readFileSync(stdout, "utf8").replace("\"code\":", "\"code\": "));
assert.equal(run().execution, "executed", "an entry whose stored result was altered");

// --- TypeScript's diagnostics replay by the same mechanism
executesThenReplays("TypeScript's diagnostics", "diagnostics");
write("dep.ts", "export function dep(x: number): string {\n  return x;\n}\n");
executesThenReplays("TypeScript's diagnostics, an imported module changed", "diagnostics");

// --- the confined compiler is killed on any read its queries do not serve
const launcher = launcherForTests();
if (launcher === null) throw Error("the compiler is not confined on this platform");
const version = spawnSync(launcher, ["--version"], { encoding: "utf8" });
assert.equal(version.status, 0, version.stderr);
const directReads: readonly (readonly [string, string])[] = [["a file", main], ["a missing file", join(fixture, "absent", "x.ts")]];
for (const [what, read] of directReads) {
  const direct: SpawnSyncReturns<string> = spawnSync(launcher, ["--noEmit", read], { encoding: "utf8" });
  assert.equal(direct.signal, "SIGKILL", `the compiler reading ${what} itself: ${JSON.stringify(direct)}`);
}
// Through the API, with directory queries the client declines.
const declining = openCompiler({ cwd: fixture, tsserverPath: launcher,
  fs: { readFile: () => undefined, fileExists: () => undefined } });
assert.throws(() => declining.updateSnapshot({ openProjects: [project] }), "a query the client declines kills the compiler");

// --- the stages' code reads the file system only through tools/files.mts
const closure = codeIdentity([join(repository, "pipeline", "parse-stage.mts")]);
const modules = Array.isArray(closure) ? closure.map((entry) => Array.isArray(entry) ? String(entry[0]) : "") : [];
assert.ok(modules.includes("tools/files.mts") && modules.includes("tools/fragment-parse.mts"), modules.join(", "));
const reading = /from "node:(fs|fs\/promises|module|child_process|worker_threads|vm)"|import\.meta\.resolve\(/;
for (const module of modules) {
  // The store's own modules read its entries, never a stage's inputs.
  if (["tools/files.mts", "pipeline/stages.mts", "pipeline/stage-store.mts", "pipeline/run-directory.mts"].includes(module))
    continue;
  const text = readFileSync(join(repository, module), "utf8").replace(/\/\/.*$|\/\*[\s\S]*?\*\//gm, "");
  assert.doesNotMatch(text, reading, `${module} reads the file system other than through tools/files.mts`);
}
process.stdout.write("observed stages: replay, invalidation, forged entries, confinement, reads in one place\n");
