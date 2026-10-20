// C2, the compiler API's guard table (COMPILER-API.md, "Binding the contract
// to the implementation"), regression evidence for its review: the
// generator's output is the reviewed table (`dev/guard-table.mts --check`),
// and every entry, run under Node on an object of each tag value (a tag
// guard on every number around the tag values), answers exactly its tag
// set, and the same with further arguments and another receiver, as a
// callback receives them.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { cpSync, readFileSync, realpathSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
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
  // Copies of the package, a manifest mapping or a module's import changed,
  // each activated exactly where Node, run in the copy, resolves the
  // specifier the change concerns to the module the table records: Node's
  // answer is the table's, whether it resolves, throws or picks another
  // file. Changes: an exact `#enums/syntaxKind` after `#enums/*`; a
  // `node-addons` key, which Node enables, and a key it does not, before
  // the entry point's module; an entry point target without `./`, or with a
  // `..` segment; an integer condition key, which Node refuses even under a
  // condition it skips; a module importing `#enums/syntaxKind/` through an
  // exact key of that spelling, or `#enums/../enums/syntaxKind`.
  const copy = (change: (manifest: Record<string, unknown>) => Record<string, unknown>,
      imported: string = "#enums/syntaxKind"): string => {
    const dir = runDirectory("tscert-guard-manifest-");
    cpSync(root, dir, { recursive: true, dereference: true });
    const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
    assert.ok(isRecord(manifest) && isRecord(manifest.imports) && isRecord(manifest.exports), "the package's manifest");
    writeFileSync(join(dir, "package.json"), JSON.stringify(change(manifest)));
    for (const module of ["dist/ast/is.js", "dist/ast/is.generated.js"]) {
      const text = readFileSync(join(dir, module), "utf8");
      writeFileSync(join(dir, module), text.replace('from "#enums/syntaxKind";', `from ${JSON.stringify(imported)};`));
    }
    return dir;
  };
  // The real path of what Node resolves `specifier` to from a module of the
  // copy, or null where it throws.
  const nodeResolves = (dir: string, specifier: string): string | null => {
    writeFileSync(join(dir, "probe.mjs"), `console.log(import.meta.resolve(${JSON.stringify(specifier)}));\n`);
    const resolved = spawnSync(process.execPath, [join(dir, "probe.mjs")], { encoding: "utf8" });
    return resolved.status === 0 ? realpathSync(fileURLToPath(resolved.stdout.trim())) : null;
  };
  const entry = (mapping: unknown) => (m: Record<string, unknown>): Record<string, unknown> =>
    ({ ...m, exports: { ...(isRecord(m.exports) ? m.exports : {}), [compilerApiGuards.entryPoint]: mapping } });
  const imports = (added: Record<string, unknown>) => (m: Record<string, unknown>): Record<string, unknown> =>
    ({ ...m, imports: { ...(isRecord(m.imports) ? m.imports : {}), ...added } });
  const point = `${hostPackage.name}${compilerApiGuards.entryPoint.slice(1)}`;
  const variants: [string, string, boolean, (m: Record<string, unknown>) => Record<string, unknown>, string?][] = [
    ["the unchanged manifest", point, true, (m) => m],
    ["an exact imports key after #enums/*", "#enums/syntaxKind", false, imports({ "#enums/syntaxKind": "./dist/enums/tokenFlags.js" })],
    ["a node-addons key", point, false, entry({ "node-addons": "./dist/ast/is.js", default: "./dist/ast/index.js" })],
    ["a key Node does not enable", point, true, entry({ "tscert-other": "./dist/ast/is.js", default: "./dist/ast/index.js" })],
    ["a target without ./", point, false, entry("dist/ast/index.js")],
    ["a target with a .. segment", point, false, entry("./dist/ast/../ast/index.js")],
    ["an integer condition key", point, false, entry({ node: { "0": "./unused.js" }, default: "./dist/ast/index.js" })],
    ["a specifier ending /", "#enums/syntaxKind/", false, imports({ "#enums/syntaxKind/": "./dist/enums/syntaxKind.js" }), "#enums/syntaxKind/"],
    ["a specifier with a .. segment", "#enums/../enums/syntaxKind", false, (m) => m, "#enums/../enums/syntaxKind"],
  ];
  for (const [what, specifier, expected, change, imported] of variants) {
    const dir = copy(change, imported);
    const reviewed = specifier === point ? compilerApiGuards.entryModule : "dist/enums/syntaxKind.js";
    const nodes = nodeResolves(dir, specifier) === realpathSync(join(dir, reviewed));
    assert.equal(nodes, expected, `${what}: Node resolves ${specifier} ${expected ? "to" : "elsewhere than"} ${reviewed}`);
    assert.equal(activeGuards(compilerApiGuards, dir)?.size === compilerApiGuards.guards.length, nodes,
      `${what}: activated exactly where Node resolves the reviewed module`);
  }
  assert.equal(activeGuards({ ...compilerApiGuards, conditions: ["node", "import", "default"] }), null,
    "conditions other than the running Node's: no table");
  console.log(`activation: the reviewed table resolves, every entry; ${mismatches.length} tables differing from the installation in one recorded fact each, and a table of other conditions than the running Node's, are none; over ${variants.length} changed copies of the package, activated exactly where Node resolves the reviewed module`);
}
