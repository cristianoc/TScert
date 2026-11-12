// Store-boundary controls over a captured fragment with implementation imports.
// node dev/module-interface-controls.mts <fragment.json> <given.jsonl> <scratch>
import { chmodSync, existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import assert from "node:assert/strict";
import { prepareInterfaces } from "../pipeline/module-interfaces.mts";
import type { InterfaceOptions } from "../pipeline/module-interfaces.mts";
import { invokeProcess } from "../pipeline/stages.mts";
import { verifierBuild, verifierCall } from "../pipeline/stage-execution.mts";
import type { Canonical } from "../pipeline/stage-execution.mts";

function record(v: unknown): Record<string, unknown> {
  if (v === null || typeof v !== "object" || Array.isArray(v)) throw Error("expected object");
  return v as Record<string, unknown>; // asserted: checked non-null, non-array object
}
function list(v: unknown): unknown[] {
  if (!Array.isArray(v)) throw Error("expected array");
  return v;
}
function parsed(path: string): Record<string, unknown> {
  const v: unknown = JSON.parse(readFileSync(path, "utf8"));
  return record(v);
}
function manifestInput(v: Canonical): string {
  return JSON.stringify(v) ?? "";
}
const [fragment, given, scratch] = process.argv.slice(2);
if (!fragment || !given || !scratch) throw Error("fragment, given, scratch required");
mkdirSync(scratch, { recursive: true });
const work = mkdtempSync(join(scratch, "interface-controls-"));
process.env.TSCERT_STAGE_STORE = join(work, "store");
const options: InterfaceOptions = { mode: 8, fuel: 12, rounds: 4096, force: [], allCuts: false, given,
  work: join(work, "first"), invocation: { limitMs: 60_000, force: false, recorder: null } };
const first = prepareInterfaces(fragment, options);
const original = readFileSync(first.path, "utf8");
const warm = prepareInterfaces(fragment, { ...options, work: join(work, "warm") });
assert(warm.records.every((r) => r.record.execution === "replayed"));
assert.equal(readFileSync(warm.path, "utf8"), original);
const component = first.records.find((r) => r.record.stage === "module-interface");
assert(component?.record.key);
const stored = join(process.env.TSCERT_STAGE_STORE, "entries", "module-interface", component.record.key, "stdout");
chmodSync(stored, 0o644);
writeFileSync(stored, '{"modules":[]}');
const repaired = prepareInterfaces(fragment, { ...options, work: join(work, "repaired") });
assert(repaired.records.some((r) => r.record.stage === "module-interface" && r.record.execution === "executed"));
assert.equal(readFileSync(repaired.path, "utf8"), original);
console.log("forged stored interface: rejected by payload integrity, recomputed");

const ast = parsed(fragment);
const modules = list(ast.modules);
assert(modules.length > 0);
const module = record(modules[0]);
module.sourceSha256 = "0".repeat(64);
const edited = join(work, "edited.json");
writeFileSync(edited, JSON.stringify(ast));
const empty = join(work, "standins.json");
writeFileSync(empty, '{"functions":[],"imports":[]}');
assert.equal(typeof ast.file, "string");
const stale = invokeProcess(verifierCall(verifierBuild, ["--verify-interface-stage", "8", edited, first.path,
  given, empty, String(ast.file), "12", ""]), options.invocation);
assert.equal(stale.status, 1);
assert(stale.stderr.includes("stale interface:"));
const changed = prepareInterfaces(edited, { ...options, work: join(work, "changed") });
assert(changed.records.some((r) => r.record.stage === "module-interface" && r.record.execution === "executed"));
assert.notEqual(readFileSync(changed.path, "utf8"), original);
console.log("module edited after publication: old interface refused; changed request misses");

// Budgets, adversarial proposals and cuts are bound, while the importer
// stage is reached only after every component has finished.
const request = first.records.find((r) => r.record.stage === "module-interface");
assert(request && manifestInput(request.record.manifest).includes("request.json"));
const forced = prepareInterfaces(fragment, { ...options, force: ["imports"], work: join(work, "forced") });
assert(forced.records.filter((r) => r.record.stage === "module-interface").every((r) => r.record.execution === "executed"));
assert.notDeepEqual(forced.records.map((r) => r.record.key), first.records.map((r) => r.record.key));
console.log("forced proposals: separate component keys");

// A normalized own-file run reaches the same complete component request.
const source = parsed(fragment);
const own = record(list(source.modules)[0]);
assert.deepEqual(own.absent, []);
const ownAst = { file: own.location, sourceSha256: own.sourceSha256, declarations: own.declarations,
  init: own.init, functions: own.functions, omittedMentions: [],
  modules: list(source.modules).filter((m) => record(m).location !== own.location) };
const ownPath = join(work, "own.json"), ownGiven = join(work, "own-given.jsonl");
const ownModule = join(work, "own-module.json");
writeFileSync(ownModule, JSON.stringify(own));
writeFileSync(ownPath, JSON.stringify(ownAst));
const prefix = `module:${String(own.location)}#`;
const lines = readFileSync(given, "utf8").split("\n").filter(Boolean).map((s) => {
  const value: unknown = JSON.parse(s), line = record(value);
  if (typeof line.unit !== "string") throw Error("missing unit");
  if (line.unit.startsWith(prefix)) line.unit = line.unit.slice(prefix.length);
  else if (!line.unit.startsWith("module:")) return null;
  return line;
}).filter((l) => l !== null);
writeFileSync(ownGiven, lines.map((l) => JSON.stringify(l)).join("\n"));
const ownResult = prepareInterfaces(ownPath, { ...options, ownModule, given: ownGiven, work: join(work, "own") });
assert.deepEqual(ownResult.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key),
  first.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key));
assert.equal(readFileSync(ownResult.path, "utf8"), original);
console.log("own-file normalization: complete component keys and results equal imported path");

const reversed = parsed(fragment);
reversed.modules = [...list(reversed.modules)].reverse();
const reversedPath = join(work, "reversed.json");
writeFileSync(reversedPath, JSON.stringify(reversed));
const reordered = prepareInterfaces(reversedPath, { ...options, work: join(work, "reordered") });
assert.deepEqual(reordered.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key),
  first.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key));
assert.equal(readFileSync(reordered.path, "utf8"), original);
console.log("importer module ordering: identical canonical component requests and results");

// Root selection cannot manufacture a partial canonical interface.
const noRoots = prepareInterfaces(fragment, { ...options, names: "%absent-interface-control",
  work: join(work, "no-roots") });
assert.deepEqual(parsed(noRoots.path), { modules: [] });
assert(noRoots.records.every((r) => r.record.stage === "interface-plan"));
const selectedOwn = prepareInterfaces(ownPath, { ...options, names: "%absent-interface-control",
  ownModule, given: ownGiven, work: join(work, "selected-own") });
assert.equal(readFileSync(selectedOwn.path, "utf8"), readFileSync(ownResult.path, "utf8"));
assert.deepEqual(selectedOwn.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key),
  ownResult.records.filter((r) => r.record.stage === "module-interface").map((r) => r.record.key));
console.log("selected roots: no unrelated component; own publication retains complete canonical keys");


// Forced executions also publish: timing text must not make one exact
// importer request produce two different stored payloads.
const importerSource = parsed(fragment);
const firstFunction = record(list(importerSource.functions)[0]);
const deterministic = verifierCall(verifierBuild, ["--verify-interface-stage", "8", fragment, first.path,
  given, empty, String(importerSource.file), "12", String(firstFunction.name)]);
const once = invokeProcess(deterministic, options.invocation);
const twice = invokeProcess(deterministic, { ...options.invocation, force: true });
assert.equal(once.stdout, twice.stdout);
assert.equal(once.stderr, twice.stderr);
assert.equal(twice.record.execution, "executed");
console.log("importer forced execution: identical semantic payload, measurement output excluded");

const timeoutRequest = parsed(join(options.work, "component-0.json"));
timeoutRequest.force = ["timeout-control"];
const timeoutPath = join(work, "timeout-request.json");
writeFileSync(timeoutPath, JSON.stringify(timeoutRequest));
const timed = invokeProcess(verifierCall(verifierBuild, ["--module-interface", timeoutPath]),
  { ...options.invocation, limitMs: 1 });
assert.equal(timed.record.execution, "timed-out");
assert(timed.record.key);
assert(!existsSync(join(process.env.TSCERT_STAGE_STORE, "entries", "module-interface", timed.record.key)));
const malformed = join(work, "malformed.json");
writeFileSync(malformed, "{}");
const failed = invokeProcess(verifierCall(verifierBuild, ["--module-interface", malformed]), options.invocation);
assert.equal(failed.record.execution, "failed");
assert(failed.record.key);
assert(!existsSync(join(process.env.TSCERT_STAGE_STORE, "entries", "module-interface", failed.record.key)));
console.log("timeout and malformed request: no finished interface published");

// A forged row: an entry whose interface type names another row of its
// module's table is not read; the importer's store-map check refuses the
// units reading it.
const published = parsed(first.path);
let forgedCount = 0;
for (const m of list(published.modules).map(record)) {
  if (m.rows === null) continue;
  const types = list(record(m.rows).types);
  for (const e of list(m.entries).map(record)) {
    if (e.established === null) continue;
    const established = record(e.established);
    const root = list(established.interface).map(Number);
    const other = types.findIndex((row, i) => !root.includes(i) && JSON.stringify(row) !== JSON.stringify(types[root[0]]));
    assert(other >= 0);
    established.interface = [other];
    forgedCount++;
  }
}
assert(forgedCount > 0, "a module with established entries");
const forgedRows = join(work, "forged-rows.json");
writeFileSync(forgedRows, JSON.stringify(published));
const rowsRun = invokeProcess(verifierCall(verifierBuild, ["--verify-interface-stage", "8", fragment, forgedRows,
  given, empty, String(ast.file), "12", ""]), options.invocation);
assert(rowsRun.stdout.includes("signature rows differ"), rowsRun.stdout + rowsRun.stderr);
console.log("forged interface rows: the importer's store-map check refuses the units reading them");
