// C2, the compiler API's guard table (COMPILER-API.md, "Binding the contract
// to the implementation"), regression evidence for its review: the
// generator's output is the reviewed table (`dev/guard-table.mts --check`),
// and every entry, run under Node on an object of each tag value (a tag
// guard on every number around the tag values), answers exactly its tag
// set, and the same with further arguments and another receiver, as a
// callback receives them.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readdirSync, readFileSync, symlinkSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { runDirectory } from "../pipeline/run-directory.mts";
import { compilerApiGuards } from "../tools/compiler-api-guards.mts";
import { activeGuards, hostPackage } from "../tools/compiler-api.mts";
import type { GuardEntry, GuardTable } from "../tools/host-families.mts";

const repository = resolve(import.meta.dirname, "..");
const generated = spawnSync(process.execPath, [join(repository, "dev", "guard-table.mts"), "--check"], { encoding: "utf8" });
assert.equal(generated.status, 0, generated.stdout + generated.stderr);

const root = dirname(createRequire(resolve(repository, "tools/package.json")).resolve(`${hostPackage.name}/package.json`));
const isRecord = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null;
const entry: unknown = await import(pathToFileURL(join(root, compilerApiGuards.entryModule)).href);
assert.ok(isRecord(entry) && isRecord(entry.SyntaxKind), "the entry point exports SyntaxKind");
const syntaxKind = entry.SyntaxKind;
const value = (name: string): number => {
  const v = syntaxKind[name];
  assert.ok(typeof v === "number", `SyntaxKind.${name}`);
  return v;
};
const tagValues = [...new Set(Object.values(syntaxKind).filter((v): v is number => typeof v === "number"))].sort((a, b) => a - b);
const max = Math.max(...tagValues);
const numbers = [...Array.from({ length: max + 5 }, (_, i) => i - 2), 0.5, -0, Number.NaN];
let calls: number = 0;
const isCallable = (v: unknown): v is (this: unknown, ...args: unknown[]) => unknown => typeof v === "function";
for (const guard of compilerApiGuards.guards) {
  const f: unknown = entry[guard.name];
  assert.ok(isCallable(f), `${guard.name} is exported`);
  const call = (receiver: unknown, args: unknown[]): unknown => f.call(receiver, ...args);
  const tags = new Set(guard.tags.map(value));
  const inputs: [unknown, boolean][] = guard.kind === "node"
    ? tagValues.map((t) => [{ kind: t }, tags.has(t)])
    : numbers.map((n) => [n, tags.has(n)]);
  const other = { kind: -1 };
  for (const [input, expected] of inputs) {
    assert.equal(call(undefined, [input]), expected, `${guard.name}(${JSON.stringify(input)})`);
    assert.equal(call(other, [input, 1, [input]]), expected, `${guard.name} with further arguments and a receiver`);
    calls += 2;
  }
}
console.log(`C2: ${compilerApiGuards.guards.length} guards, ${calls} calls under Node, each answering exactly its tag set; ` +
  `${compilerApiGuards.excluded.length} declared guards outside the contract: ${compilerApiGuards.excluded.map(([n]) => n).join(", ")}`);

// The table's activation (HOST-FAMILIES.md, "The guard table"): the reviewed
// table resolves as recorded over the installation, every entry; a table
// differing from the installation in any recorded resolution fact (its entry
// module, conditions or `imports` mapping; an entry's module, chain or text;
// a helper's text; the helpers or binding edges its closure reaches) is no
// table.
{
  const active = activeGuards(compilerApiGuards);
  assert.ok(active && active.size === compilerApiGuards.guards.length, "the reviewed table resolves, every entry");
  const named = (name: string): GuardEntry => {
    const found = compilerApiGuards.guards.find(g => g.name === name);
    assert.ok(found, name);
    return found;
  };
  const identifier = named("isIdentifier");
  const helped = compilerApiGuards.guards.find(g => g.helpers.length > 0);
  assert.ok(helped, "an entry with a helper");
  const [helper] = helped.helpers;
  assert.ok(helper !== undefined, "its helper");
  const one = (entry: GuardEntry): GuardTable => ({ ...compilerApiGuards, guards: [entry] });
  const mismatches: [string, GuardTable][] = [
    ["another entry module", { ...compilerApiGuards, entryModule: "dist/ast/is.js" }],
    ["other conditions", { ...compilerApiGuards, conditions: ["browser"] }],
    ["another imports mapping", { ...compilerApiGuards, imports: { "#enums/*": { default: "./dist/ast/*.js" } } }],
    ["another module", one({ ...identifier, module: "dist/ast/is.js" })],
    ["another chain", one({ ...identifier, chain: [compilerApiGuards.entryModule, identifier.module] })],
    ["another text", one({ ...identifier, text: identifier.text.replace("===", "!==") })],
    ["a helper more", one({ ...identifier, helpers: [helper] })],
    ["a helper less", one({ ...helped, helpers: helped.helpers.slice(1) })],
    ["an edge less", one({ ...identifier, edges: [] })],
    ["another helper text", { ...one(helped), helpers: { ...compilerApiGuards.helpers, [helper]: "function f() {}" } }],
  ];
  for (const [what, table] of mismatches)
    assert.equal(activeGuards(table), null, `${what}: no table`);
  // A manifest override: the package's own entries, its manifest's
  // `imports` with an exact `#enums/syntaxKind` after the reviewed
  // `#enums/*`. Node resolves the exact key, so the reviewed table is no
  // table there; the unchanged manifest's copy activates it.
  const copy = (imports: (recorded: Record<string, unknown>) => Record<string, unknown>): string => {
    const dir = runDirectory("tscert-guard-manifest-");
    for (const name of readdirSync(root)) if (name !== "package.json") symlinkSync(join(root, name), join(dir, name));
    const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
    assert.ok(isRecord(manifest) && isRecord(manifest.imports), "the package's manifest has imports");
    writeFileSync(join(dir, "package.json"), JSON.stringify({ ...manifest, imports: imports(manifest.imports) }));
    return dir;
  };
  assert.ok(activeGuards(compilerApiGuards, copy((m) => m))?.size === compilerApiGuards.guards.length,
    "the reviewed table resolves over the unchanged manifest's copy");
  const overridden = copy((m) => ({ ...m, "#enums/syntaxKind": "./dist/enums/tokenFlags.js" }));
  writeFileSync(join(overridden, "probe.mjs"), `console.log(import.meta.resolve("#enums/syntaxKind"));\n`);
  const resolved = spawnSync(process.execPath, [join(overridden, "probe.mjs")], { encoding: "utf8" });
  assert.match(resolved.stdout, /dist\/enums\/tokenFlags\.js/, `Node resolves the exact key: ${resolved.stdout}${resolved.stderr}`);
  assert.equal(activeGuards(compilerApiGuards, overridden), null, "an exact imports key after the reviewed pattern: no table");
  console.log(`activation: the reviewed table resolves, every entry; ${mismatches.length} tables differing from the installation in one recorded fact each, and a manifest whose exact imports key Node prefers to the reviewed pattern, are none`);
}
