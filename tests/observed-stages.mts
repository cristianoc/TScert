// The observed stages' tests (DESIGN.md, "Observed stages"): a parse
// replays after an unchanged run, and a change to an imported module, to a
// declaration file reached through node_modules, to the tsconfig, to the
// family descriptions or to the TypeScript package, and a module added where
// it changes resolution, each make it execute; forged entries are refused;
// TypeScript's diagnostics replay by the same mechanism. The confined
// compiler is killed on a read the API's queries do not serve, and the stages'
// code reads the file system only through tools/files.mts. Replay controls
// use fresh processes, and the parse's run real compilers: they are a suite
// of pipeline/test.mts. The retirement control reuses one process.
// --node-only runs the controls that do not require sandbox-exec; --reads
// only the check that the stages' code reads through tools/files.mts, a fast
// check of test-all.sh.
import assert from "node:assert/strict";
import { spawnSync, type SpawnSyncReturns } from "node:child_process";
import { chmodSync, cpSync, mkdirSync, readdirSync, readFileSync, rmSync, symlinkSync, unlinkSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { runDirectory } from "../pipeline/run-directory.mts";
import { Recorder, invokeInProcess } from "../pipeline/stages.mts";
import { captureCodeIdentity, codeIdentity, sha256, type Canonical } from "../pipeline/stage-execution.mts";
import { textCodec } from "../pipeline/in-process-execution.mts";
import { Store } from "../pipeline/stage-store.mts";
import { compilerImplementation, launcherForTests, openCompiler, useInstallationForTests } from "../tools/compiler-channel.mts";
import { nodeResolve, processRetirement, observed, observationsHold, type Observation } from "../tools/files.mts";

const here = import.meta.dirname;
const repository = resolve(here, "..");

// --- the keyed closures: identified, and outside the policy; the stages'
// code reads the file system only through tools/files.mts
if (process.argv[2] === "--reads") {
  const closureOf = (root: string, packages: readonly string[] = []): string[] => {
    const closure = codeIdentity([join(repository, root)], packages);
    assert.ok("identity" in closure, `${root}: ${"unidentified" in closure ? closure.unidentified : ""}`);
    const listed = closure.identity;
    return Array.isArray(listed) ? listed.map((entry) => Array.isArray(entry) ? String(entry[0]) : "") : [];
  };
  // The policy, the store and the orchestration decide no stage's result
  // (DESIGN.md, "The stage store", keys): no key covers them.
  const unkeyed = ["pipeline/stages.mts", "pipeline/stage-store.mts", "pipeline/verify-source.mts"];
  const roots: [string, readonly string[]][] = [["pipeline/stage-execution.mts", []], ["pipeline/in-process-execution.mts", []],
    ["pipeline/parse-stage.mts", ["typescript"]], ["pipeline/claims-assembly.mts", []]];
  for (const [root, packages] of roots) {
    const listed = closureOf(root, packages);
    for (const module of unkeyed) assert.ok(!listed.includes(module), `${root}'s closure holds ${module}`);
  }
  // A load the scan does not read leaves the code unidentified; a load in a
  // comment or a string, and a relative path it follows, do not.
  const scratch = runDirectory("loads-");
  const loads: [string, boolean][] = [
    ['const n = 1 / (await import(name)).n / 2;', false],
    ['const s = `${/}/.test("}") ? import(name) : 0}`;', false],
    ['const s = `${/[}]/.test("}") ? import(name) : 0}`;', false],
    ['const s = `${1 / (await import(name)).n / 2}`;', false],
    ['const n = 1 / require(name).n / 2;', false],
    ['const n = 1 / 2 /import(name);', false],
    ['if (true) /"/.test("x"); await import(name);', false],
    ['const s = `${(() => { if (true) /}/.test("}"); return import(name); })()}`;', false],
    ['const r = /import(name)/;', false],
    ['const m = await import(name);', false], ['const m = require("x");', false], ['(0, eval)("1");', false],
    ['new Function("return 1");', false], ['import vm from "node:vm";', false], ['import ts from "left-pad";', false],
    ['import x from "/abs/x.mts";', false], ['import x from "./missing.mts";', false], ['const s = "unterminated\n";', false],
    ['// import(name); require("x"); eval\nconst s = "import(name) require( eval";', true],
    ['import { join } from "node:path";\nimport { y } from "./dep.mts";\nconst r = /["`]/;', true]];
  writeFileSync(join(scratch, "dep.mts"), "export const y = 1;\n");
  for (const [i, [text, identified]] of loads.entries()) {
    const module = join(scratch, `load-${i}.mts`);
    writeFileSync(module, text + "\n");
    assert.equal("identity" in codeIdentity([module]), identified, text);
  }
  const processAdapter = closureOf("pipeline/stage-execution.mts");
  for (const module of ["tools/files.mts", "tools/compiler-channel.mts"])
    assert.ok(!processAdapter.includes(module), `the process adapter's closure holds ${module}`);
  const modules = closureOf("pipeline/parse-stage.mts", ["typescript"]);
  assert.ok(modules.includes("tools/files.mts") && modules.includes("tools/fragment-parse.mts"), modules.join(", "));
  const reading = /(?:\bfrom\s*|\bimport\s*(?:\(\s*)?)["'](?:node:)?(?:fs(?:\/promises)?|module|child_process|worker_threads|vm)["']|import\s*\.\s*meta\s*\.\s*resolve\s*\(/;
  for (const specifier of ["fs", "fs/promises", "module", "child_process", "worker_threads", "vm"]) {
    for (const prefix of ["", "node:"]) for (const quote of ['"', "'"]) {
      const literal = quote + prefix + specifier + quote;
      for (const source of [`import x from ${literal};`, `import ${literal};`, `await import(${literal});`])
        assert.match(source, reading, source);
    }
  }
  for (const module of modules) {
    // The execution adapters read the code they identify and a process
    // stage's inputs, never an observed stage's.
    if (["tools/files.mts", "pipeline/stage-execution.mts", "pipeline/run-directory.mts"].includes(module))
      continue;
    const text = readFileSync(join(repository, module), "utf8");
    assert.doesNotMatch(text, reading, `${module} reads the file system other than through tools/files.mts`);
  }
  process.stdout.write("observed stages: the keyed closures are identified and hold no policy, store or orchestration module; " +
    "the stages' code reads the file system only through tools/files.mts\n");
  process.exit(0);
}

// A run of one observed stage in this process, printed as its attempt.
if (process.argv[2] === "--run") {
  const [stage, source, project, families, installation] = process.argv.slice(3);
  // A child loads the front end only where its stage uses it.
  if (families === "changed") {
    const { compilerApiFamily } = await import("../tools/compiler-api.mts");
    const { useFamiliesForTests } = await import("../tools/family-activation.mts");
    useFamiliesForTests([{ ...compilerApiFamily, corrections: compilerApiFamily.corrections.slice(1) }]);
  }
  if (installation !== "-") useInstallationForTests(installation);
  const recorder = new Recorder(null);
  if (stage === "resolution" || stage === "mutation") {
    invokeInProcess({ stage: "parse", implementation: captureCodeIdentity([]),
      inputs: [{ role: "control", bytes: stage + source + families }], observed: { compiler: compilerImplementation }, codec: textCodec,
      run: (): string => {
        if (stage === "resolution") return nodeResolve(families, source) ?? "unresolved";
        const path = join(installation, "node_modules", "typescript", "package.json");
        writeFileSync(path, readFileSync(path, "utf8") + "\n");
        return "installation changed during execution";
      } }, { force: false, recorder });
  } else {
    const { parseSource, typeScriptErrors } = await import("../pipeline/verify-source.mts");
    if (stage === "diagnostics") typeScriptErrors(recorder, source, project);
    else parseSource(source, project, runDirectory("observed-"), recorder);
  }
  const record = recorder.records.find((r) => r.stage === (stage === "resolution" || stage === "mutation" ? "parse" : stage));
  process.stdout.write(JSON.stringify({ execution: record?.execution, ineligible: record?.ineligible, key: record?.key }));
  process.exit(0);
}

if (process.argv[2] === "--resolve") {
  process.stdout.write(nodeResolve(process.argv[3], process.argv[4]) ?? "unresolved");
  process.exit(0);
}

// An incomplete resolution can populate Node's caches without observing the
// link target. Later execution must be refused even when every observation holds.
if (process.argv[2] === "--retarget") {
  const directory = process.argv[3];
  const parent = join(directory, "main.ts");
  const inward = process.argv[4] === "#guard";
  const specifier = inward ? "#guard" : "exported";
  const reason = inward ? /non-relative target/ : /symbolic link/;
  const target = join(directory, inward ? "node_modules/redirected/target.js" : "node_modules/exported/target.js");
  const implementation = captureCodeIdentity([]);
  const invoke = (name: string, run: () => string): ReturnType<typeof invokeInProcess<string>> =>
    invokeInProcess({ stage: "parse", implementation, inputs: [{ role: "control", bytes: name }],
      observed: { compiler: compilerImplementation }, codec: textCodec, run }, { force: false, recorder: null });
  const stable = (): string => "independent replay";
  assert.equal(invoke("stable", stable).record.execution, "executed");
  let observations: readonly Observation[] = [];
  const first = invoke("linked", () => {
    const made = observed(() => nodeResolve(specifier, parent) ?? "unresolved");
    observations = made.observations;
    return made.value;
  });
  assert.match(first.value, inward ? /\/a\.js$/ : /third\.js$/);
  assert.equal(first.record.execution, "executed");
  assert.equal(first.record.key, null);
  assert.match(first.record.ineligible ?? "", reason);
  assert.match(processRetirement() ?? "", reason);
  rmSync(target);
  symlinkSync(inward ? "../../b.js" : "other.js", target);
  assert.equal(observationsHold(observations), true);
  const fresh = spawnSync(process.execPath, [import.meta.filename, "--resolve", specifier, parent], { encoding: "utf8" });
  assert.equal(fresh.status, 0, fresh.stderr);
  assert.match(fresh.stdout, inward ? /\/b\.js$/ : /other\.js$/);
  let executed = false;
  assert.throws(() => invoke("linked", () => {
    executed = true;
    return nodeResolve(specifier, parent) ?? "unresolved";
  }), /fresh process is needed/);
  assert.equal(executed, false);
  assert.equal(invoke("stable", stable).record.execution, "replayed");
  process.exit(0);
}

// A scope link can change while both package trees and manifests stay intact.
if (process.argv[2] === "--retarget-scope") {
  const directory = process.argv[3], specifier = process.argv[4];
  const link = join(directory, "link"), parent = join(link, "main.js");
  const implementation = captureCodeIdentity([]);
  let observations: readonly Observation[] = [];
  const invoke = (): ReturnType<typeof invokeInProcess<string>> =>
    invokeInProcess({ stage: "parse", implementation,
      inputs: [{ role: "control", bytes: parent + specifier }], observed: { compiler: compilerImplementation }, codec: textCodec,
      run: (): string => {
        const made = observed(() => nodeResolve(specifier, parent) ?? "unresolved");
        observations = made.observations;
        return made.value;
      } }, { force: false, recorder: null });
  const first = invoke();
  assert.equal(first.record.execution, "executed");
  assert.equal(first.record.ineligible, null);
  assert.match(first.value, /\/a\/target\.js$/);
  assert.equal(observationsHold(observations), true);
  unlinkSync(link);
  symlinkSync("b", link);
  assert.equal(observationsHold(observations), false);
  const fresh = spawnSync(process.execPath, [import.meta.filename, "--resolve", specifier, parent], { encoding: "utf8" });
  assert.equal(fresh.status, 0, fresh.stderr);
  assert.match(fresh.stdout, /\/b\/target\.js$/);
  assert.throws(invoke, /fresh process is needed/);
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
function run(stage: "parse" | "diagnostics" | "resolution" | "mutation" = "parse", families: string = "reviewed", installation: string = "-", parent: string = main): Attempt {
  const p = spawnSync(process.execPath, [import.meta.filename, "--run", stage, parent, project, families, installation],
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

const installation = join(dir, "installation");
for (const name of ["typescript", "@typescript"])
  cpSync(join(repository, "tools", "node_modules", name), join(installation, "node_modules", name), { recursive: true });

// --- publication requires the compiler identity after the stage's run
const mutated = run("mutation", "reviewed", installation);
assert.equal(mutated.execution, "executed");
assert.match(mutated.ineligible ?? "", /compiler differs/);
assert.equal(mutated.key, null);

// --- Node resolution, through the same observed-stage entry point
// The compiler package's conditional and wildcard imports remain replayable.
for (const specifier of ["#getExePath", "#enums/characterCodes", "#vscode-jsonrpc/node"]) {
  const parent = join(installation, "node_modules/typescript/dist/api/sync/api.js");
  const attempt = run("resolution", specifier, "-", parent);
  assert.equal(attempt.execution, "executed");
  assert.equal(attempt.ineligible, null);
  assert.equal(run("resolution", specifier, "-", parent).execution, "replayed");
}

write("node_modules/exported/package.json", JSON.stringify({ name: "exported", exports: "./target.js" }));
write("node_modules/exported/target.js", "export {};\n");
write("node_modules/exported/other.js", "export {};\n");
write("node_modules/exported/target.d.ts", "export declare const x: number;\n");
write("node_modules/exported/other.d.ts", "export declare const x: string;\n");
assert.equal(run("resolution", "exported").ineligible, null);
assert.equal(run("resolution", "exported").execution, "replayed");
const target = join(fixture, "node_modules/exported/target.js");
rmSync(target);
symlinkSync("other.js", target);
const linked = run("resolution", "exported");
assert.equal(linked.execution, "executed", "inserting an export-target link invalidates the directory observation");
assert.match(linked.ineligible ?? "", /symbolic link/);
write("node_modules/exported/third.js", "export {};\n");
rmSync(target);
symlinkSync("third.js", target);
assert.match(run("resolution", "exported").ineligible ?? "", /symbolic link/);

const retarget = spawnSync(process.execPath, [import.meta.filename, "--retarget", fixture],
  { encoding: "utf8", env: { ...process.env, TSCERT_STAGE_STORE: root } });
assert.equal(retarget.status, 0, retarget.stderr);

// Imports and self-references bind the real directory of a symlinked scope,
// even when its manifests, entries and the original target stay unchanged.
for (const specifier of ["#local", "scope-self"]) {
  const directory = join(dir, specifier === "#local" ? "import-scope" : "self-scope");
  for (const name of ["a", "b"]) {
    mkdirSync(join(directory, name), { recursive: true });
    writeFileSync(join(directory, name, "package.json"), JSON.stringify({
      name: "scope-self", exports: "./target.js", imports: { "#local": "./target.js" },
    }));
    for (const file of ["main.js", "target.js"])
      writeFileSync(join(directory, name, file), "export {};\n");
  }
  const link = join(directory, "link"), parent = join(link, "main.js");
  symlinkSync("a", link);
  const first = run("resolution", specifier, "-", parent);
  assert.equal(first.execution, "executed");
  assert.equal(first.ineligible, null);
  assert.equal(run("resolution", specifier, "-", parent).execution, "replayed");
  unlinkSync(link);
  symlinkSync("b", link);
  const second = run("resolution", specifier, "-", parent);
  assert.equal(second.execution, "executed");
  assert.equal(second.ineligible, null);
  assert.notEqual(second.key, first.key);
  assert.equal(run("resolution", specifier, "-", parent).execution, "replayed");
  unlinkSync(link);
  symlinkSync("a", link);
  const stale = spawnSync(process.execPath, [import.meta.filename, "--retarget-scope", directory, specifier],
    { encoding: "utf8", env: { ...process.env, TSCERT_STAGE_STORE: join(directory, "store") } });
  assert.equal(stale.status, 0, stale.stderr);
}

// Null exports do not establish a self-reference. A scope search stops at
// node_modules, even when the containing project names the requested package.
for (const boundary of [false, true]) {
  const name = boundary ? "boundary" : "null-self";
  write("package.json", JSON.stringify({ name, exports: boundary ? "./local.js" : null }));
  write("local.js", "export {};\n");
  const parent = boundary ? join(fixture, "node_modules/unscoped/main.js") : main;
  if (boundary) write("node_modules/unscoped/main.js", "export {};\n");
  write(`node_modules/${name}/a.js`, "export {};\n");
  write(`node_modules/${name}/b.js`, "export {};\n");
  for (const target of ["a.js", "b.js"]) {
    write(`node_modules/${name}/package.json`, JSON.stringify({ name, exports: `./${target}` }));
    const attempt = run("resolution", name, "-", parent);
    assert.equal(attempt.execution, "executed");
    assert.equal(attempt.ineligible, null);
    assert.equal(run("resolution", name, "-", parent).execution, "replayed");
  }
}
write("node_modules/null-exports/package.json", JSON.stringify({ exports: null, main: "index.js" }));
write("node_modules/null-exports/index.js", "export {};\n");
assert.match(run("resolution", "null-exports").ineligible ?? "", /states no exports/);

// A package import to the scope's own file replays; one redirected to another
// package lookup is not accounted for.
write("package.json", JSON.stringify({ imports: { "#local": { default: ["./local.js"] } } }));
write("local.js", "export {};\n");
assert.equal(run("resolution", "#local").ineligible, null);
assert.equal(run("resolution", "#local").execution, "replayed");
write("package.json", JSON.stringify({ imports: { "#guard": { default: ["redirected/guard"] }, "#local": "./local.js" } }));
assert.match(run("resolution", "#local").ineligible ?? "", /non-relative target/);
const external = join(dir, "node_modules/redirected");
mkdirSync(external, { recursive: true });
writeFileSync(join(external, "package.json"), JSON.stringify({ exports: { "./guard": "./a.js" } }));
writeFileSync(join(external, "a.js"), "export {};\n");
writeFileSync(join(external, "b.js"), "export {};\n");
const incompleteImport = (): void => {
  const attempt = run("resolution", "#guard");
  assert.equal(attempt.execution, "executed");
  assert.match(attempt.ineligible ?? "", /non-relative target/);
  assert.equal(attempt.key, null);
};
incompleteImport();
writeFileSync(join(external, "package.json"), JSON.stringify({ exports: { "./guard": "./b.js" } }));
incompleteImport();
write("node_modules/redirected/package.json", JSON.stringify({ exports: { "./guard": "./near.js" } }));
write("node_modules/redirected/near.js", "export {};\n");
incompleteImport();
// The redirected package's link points inward; retargeting preserves every
// recorded answer, but fresh resolution changes and the worker must retire.
write("a.js", "export {};\n");
write("b.js", "export {};\n");
write("node_modules/redirected/package.json", JSON.stringify({ exports: { "./guard": "./target.js" } }));
symlinkSync("../../a.js", join(fixture, "node_modules/redirected/target.js"));
const inwardRetarget = spawnSync(process.execPath, [import.meta.filename, "--retarget", fixture, "#guard"],
  { encoding: "utf8", env: { ...process.env, TSCERT_STAGE_STORE: join(dir, "inward-store") } });
assert.equal(inwardRetarget.status, 0, inwardRetarget.stderr);
rmSync(join(fixture, "package.json"));
rmSync(join(fixture, "local.js"));

if (process.argv[2] !== "--node-only") {
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

}

process.stdout.write(process.argv[2] === "--node-only"
  ? "observed stages: Node resolution, retirement, compiler identity\n"
  : "observed stages: replay, invalidation, forged entries, confinement\n");
