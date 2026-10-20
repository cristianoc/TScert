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
import { activeGuards, hostPackage, importsKey } from "../tools/compiler-api.mts";
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
  // Manifest overrides: copies of the package, its own entries beside a
  // manifest changed in one mapping, each resolved by Node from a module of
  // the copy and activated or not as Node's choice is the reviewed module or
  // not. An exact `#enums/syntaxKind` after the reviewed `#enums/*`, and a
  // `node-addons` key before the entry point's module, are Node's choice
  // and no table; a key Node does not enable is skipped by both.
  const copy = (change: (manifest: Record<string, unknown>) => Record<string, unknown>): string => {
    const dir = runDirectory("tscert-guard-manifest-");
    for (const name of readdirSync(root)) if (name !== "package.json") symlinkSync(join(root, name), join(dir, name));
    const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
    assert.ok(isRecord(manifest) && isRecord(manifest.imports) && isRecord(manifest.exports), "the package's manifest");
    writeFileSync(join(dir, "package.json"), JSON.stringify(change(manifest)));
    return dir;
  };
  // What Node resolves `specifier` to from a module of the copy.
  const nodeResolves = (dir: string, specifier: string): string => {
    writeFileSync(join(dir, "probe.mjs"), `console.log(import.meta.resolve(${JSON.stringify(specifier)}));\n`);
    const resolved = spawnSync(process.execPath, [join(dir, "probe.mjs")], { encoding: "utf8" });
    assert.equal(resolved.status, 0, resolved.stderr);
    return resolved.stdout.trim();
  };
  const entry = (mapping: unknown) => (m: Record<string, unknown>): Record<string, unknown> =>
    ({ ...m, exports: { ...(isRecord(m.exports) ? m.exports : {}), [compilerApiGuards.entryPoint]: mapping } });
  assert.ok(activeGuards(compilerApiGuards, copy((m) => m))?.size === compilerApiGuards.guards.length,
    "the reviewed table resolves over the unchanged manifest's copy");
  const overridden = copy((m) => ({ ...m, imports: { ...(isRecord(m.imports) ? m.imports : {}), "#enums/syntaxKind": "./dist/enums/tokenFlags.js" } }));
  assert.match(nodeResolves(overridden, "#enums/syntaxKind"), /dist\/enums\/tokenFlags\.js$/, "Node resolves the exact key");
  assert.equal(activeGuards(compilerApiGuards, overridden), null, "an exact imports key after the reviewed pattern: no table");
  const addons = copy(entry({ "node-addons": "./dist/ast/is.js", default: "./dist/ast/index.js" }));
  assert.match(nodeResolves(addons, `${hostPackage.name}/unstable/ast`), /dist\/ast\/is\.js$/, "Node enables node-addons");
  assert.equal(activeGuards(compilerApiGuards, addons), null, "a node-addons key before the reviewed module: no table");
  const skipped = copy(entry({ "tscert-other": "./dist/ast/is.js", default: "./dist/ast/index.js" }));
  assert.match(nodeResolves(skipped, `${hostPackage.name}/unstable/ast`), /dist\/ast\/index\.js$/, "Node skips a key it does not enable");
  assert.ok(activeGuards(compilerApiGuards, skipped)?.size === compilerApiGuards.guards.length, "a key Node does not enable, skipped");
  assert.equal(activeGuards({ ...compilerApiGuards, conditions: ["node", "import", "default"] }), null,
    "conditions other than the running Node's: no table");
  // Internal specifiers Node refuses (`#`, `#/…`, a trailing `/`, a `..` or
  // `node_modules` segment) have no key; a backslash, a `%` and an empty
  // segment, which Node resolves decoded or deprecated, have none either;
  // a plain match is Node's.
  const specifiers = copy((m) => ({ ...m, imports: { "#x/": "./slash.js", "#x/*": "./*.js", "#": "./h.js", "#/*": "./h/*.js" } }));
  const keys = ["#x/", "#x/*", "#", "#/*"];
  for (const specifier of ["#x/", "#x/a/", "#", "#/a", "#x/../a", "#x/node_modules/a", "#x/%2e%2e/a"]) {
    assert.throws(() => nodeResolves(specifiers, specifier), `Node refuses ${specifier}`);
    assert.equal(importsKey(keys, specifier), null, `${specifier}: no key`);
  }
  for (const specifier of ["#x//a", "#x/a\\b"]) assert.equal(importsKey(keys, specifier), null, `${specifier}: no key`);
  assert.match(nodeResolves(specifiers, "#x/a"), /\/a\.js$/, "Node resolves #x/a through #x/*");
  assert.deepEqual(importsKey(keys, "#x/a"), { key: "#x/*", star: "a" }, "#x/a: the key Node selects");
  console.log(`activation: the reviewed table resolves, every entry; ${mismatches.length} tables differing from the installation in one recorded fact each, a table of other conditions than the running Node's, and manifests whose exact imports key or node-addons key Node prefers, are none; internal specifiers Node refuses have no key`);
}
