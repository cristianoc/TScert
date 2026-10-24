// C2, a family's guard table (HOST-FAMILIES.md, "The guard table";
// COMPILER-API.md, "Binding the contract to the implementation"), regression
// evidence for its review, of the compiler API's table and the string-tagged
// stand-in's alike: the generator's output is the reviewed table
// (`dev/guard-table.mts`, `--check` for the compiler API's module), and every
// entry, run under Node on an object of each tag value (a tag guard on every
// value around the tag values), answers exactly its tag set, and the same
// with further arguments and another receiver, as a callback receives them;
// and on `undefined`, each entry behaves as its `onUndefined` states.
import assert from "node:assert/strict";
import { isDeepStrictEqual } from "node:util";
import { spawnSync } from "node:child_process";
import { cpSync, existsSync, mkdirSync, readFileSync, realpathSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { runDirectory } from "../pipeline/run-directory.mts";
import { linkFixtures } from "../pipeline/fixture-links.mts";
import { stringFamily } from "../pipeline/string-family.mts";
import { guardTable } from "../dev/guard-table.mts";
import { compilerApiGuards } from "../tools/compiler-api-guards.mts";
import { compilerApiFamily, hostPackage } from "../tools/compiler-api.mts";
import { activeGuards, importedGuard, installationRoot, useFamiliesForTests } from "../tools/family-activation.mts";
import { close as closeParser } from "../tools/fragment-parse.mts";
import type { FamilyDescription, GuardEntry, GuardTable } from "../tools/host-families.mts";

const repository = resolve(import.meta.dirname, "..");
const generated = spawnSync(process.execPath, [join(repository, "dev", "guard-table.mts"), "--check"], { encoding: "utf8" });
assert.equal(generated.status, 0, generated.stdout + generated.stderr);
linkFixtures();
assert.ok(isDeepStrictEqual(await guardTable(stringFamily), stringFamily.guards), "the stand-in's table is the generator's output");
closeParser();

const root = dirname(createRequire(resolve(repository, "tools/package.json")).resolve(`${hostPackage.name}/package.json`));
const isRecord = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null;
const isCallable = (v: unknown): v is (this: unknown, ...args: unknown[]) => unknown => typeof v === "function";
/** Every entry of a family's table under Node, on an object of each tag
 * value and, for a tag guard, on every value around them; the calls made. */
const runEntries = async (description: FamilyDescription): Promise<number> => {
  const table = description.guards;
  const entry: unknown = await import(pathToFileURL(join(installationRoot(description), table.entryModule)).href);
  const enumName = description.tag.constants.enum;
  const tagEnum: unknown = isRecord(entry) ? entry[enumName] : undefined;
  assert.ok(isRecord(entry) && isRecord(tagEnum), `the entry point exports ${enumName}`);
  const value = (name: string): unknown => {
    const v = tagEnum[name];
    assert.ok(typeof v === description.tag.primitive, `${enumName}.${name}`);
    return v;
  };
  const tagValues = [...new Set(Object.values(tagEnum).filter((v) => typeof v === description.tag.primitive))];
  const numeric = tagValues.filter((v): v is number => typeof v === "number");
  const around: unknown[] = description.tag.primitive === "number"
    ? [...Array.from({ length: Math.max(...numeric) + 5 }, (_, i) => i - 2), 0.5, -0, Number.NaN]
    : [...tagValues, "", "other", ...Object.keys(tagEnum)];
  let calls = 0;
  for (const guard of table.guards) {
    const f: unknown = entry[guard.name];
    assert.ok(isCallable(f), `${guard.name} is exported`);
    const call = (receiver: unknown, args: unknown[]): unknown => f.call(receiver, ...args);
    const tags = new Set(guard.tags.map(value));
    const inputs: [unknown, boolean][] = guard.kind === "node"
      ? tagValues.map((t) => [{ [description.tag.field]: t }, tags.has(t)])
      : around.map((n) => [n, tags.has(n)]);
    const other = { [description.tag.field]: -1 };
    for (const [input, expected] of inputs) {
      assert.equal(call(undefined, [input]), expected, `${guard.name}(${JSON.stringify(input)})`);
      assert.equal(call(other, [input, 1, [input]]), expected, `${guard.name} with further arguments and a receiver`);
      calls += 2;
    }
    // Its audited behaviour on `undefined` (HOST-FAMILIES.md, "Undefined
    // arguments"), with and without further arguments and a receiver: a
    // `TypeError`, or `false`. An unadmitted entry states none.
    if (guard.onUndefined !== "unadmitted") {
      const runs: (() => unknown)[] = [() => call(undefined, [undefined]), () => call(other, [undefined, 1, []])];
      for (const run of runs) {
        if (guard.onUndefined === "throws") assert.throws(run, TypeError, `${guard.name}(undefined) throws a TypeError`);
        else assert.equal(run(), false, `${guard.name}(undefined) answers false`);
        calls += 1;
      }
    }
  }
  return calls;
};
for (const description of [compilerApiFamily, stringFamily]) {
  const calls = await runEntries(description);
  console.log(`C2, ${description.marker}: ${description.guards.guards.length} guards as generated, ${calls} calls under Node, each answering exactly its tag set and behaving on undefined as recorded; ` +
    `${description.guards.excluded.length} declared guards outside the contract: ${description.guards.excluded.map(([n]) => n).join(", ")}`);
}
// Descriptions forged to state another behaviour on `undefined`: a node
// guard that throws stated `false`, a tag guard answering `false` stated
// `throws`, and an entry for `isNameOrAbsent`, which answers `true` there,
// stated `false`; each fails the run under Node.
{
  const named = (name: string): GuardEntry => {
    const found = stringFamily.guards.guards.find(g => g.name === name);
    assert.ok(found, name);
    return found;
  };
  const forged: [string, GuardEntry][] = [
    ["isName stated false", { ...named("isName"), onUndefined: "false" }],
    ["isNameType stated throws", { ...named("isNameType"), onUndefined: "throws" }],
    ["isNameOrAbsent stated false", { ...named("isName"), name: "isNameOrAbsent", onUndefined: "false",
      text: "export function isNameOrAbsent(node) {\n    return node === undefined || node.type === UnitType.Name;\n}" }],
  ];
  for (const [what, entry] of forged)
    await assert.rejects(runEntries({ ...stringFamily, guards: { ...stringFamily.guards, guards: [entry] } }),
      `${what}: the run under Node refuses it`);
  console.log(`C2, forged behaviour on undefined: ${forged.map(([w]) => w).join(", ")}, each refused under Node`);
}

// The table's activation (HOST-FAMILIES.md, "The guard table"): the reviewed
// table resolves as recorded over the installation, every entry; a table
// differing from the installation in any recorded resolution fact (its entry
// module, conditions or `imports` mapping; an entry's module, chain or text;
// a helper's text; the helpers or binding edges its closure reaches) is no
// table.
{
  const active = activeGuards(compilerApiGuards, root);
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
    ["an executable module less", { ...compilerApiGuards, closure: { ...compilerApiGuards.closure, files: {} } }],
    ["an executable edge less", { ...compilerApiGuards, closure: { ...compilerApiGuards.closure, edges: compilerApiGuards.closure.edges.slice(1) } }],
    ["another executable digest", { ...compilerApiGuards, closure: { ...compilerApiGuards.closure,
      files: { ...compilerApiGuards.closure.files, [compilerApiGuards.entryModule]: "0".repeat(64) } } }],
    ["other conditions", { ...compilerApiGuards, conditions: ["browser"] }],
    ["another module", one({ ...identifier, module: "dist/ast/is.js" })],
    ["another text", one({ ...identifier, text: identifier.text.replace("===", "!==") })],
    ["a helper more", one({ ...identifier, helpers: [helper] })],
    ["a helper less", one({ ...helped, helpers: helped.helpers.slice(1) })],
    ["an edge less", one({ ...identifier, edges: [] })],
    ["another helper text", { ...one(helped), helpers: { ...compilerApiGuards.helpers, [helper]: "function f() {}" } }],
  ];
  for (const [what, table] of mismatches)
    assert.equal(activeGuards(table, root), null, `${what}: no table`);
  // Copies of the package, a manifest mapping or a module's import changed,
  // each activated exactly where Node, run in the copy, resolves the
  // specifier the change concerns to the module the table records: Node's
  // answer is the table's, whether it resolves, throws or picks another
  // file. Changes: an exact `#enums/syntaxKind` after `#enums/*`; a
  // `node-addons` key, which Node enables, and a key it does not, before
  // the entry point's module; an entry point target without `./`, or with a
  // `..` segment; an integer condition key, which Node refuses even under a
  // condition it skips; a module importing `#enums/syntaxKind/` through an
  // exact key of that spelling, or `#enums/../enums/syntaxKind`; and an
  // enum import Node cannot load, of a name the enum module does not
  // export, or with JSON attributes. Node's answer is what it loads.
  const copy = (change: (manifest: Record<string, unknown>) => Record<string, unknown>,
      line: string = 'import { SyntaxKind } from "#enums/syntaxKind";'): string => {
    const dir = runDirectory("tscert-guard-manifest-");
    cpSync(root, dir, { recursive: true, dereference: true });
    const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
    assert.ok(isRecord(manifest) && isRecord(manifest.imports) && isRecord(manifest.exports), "the package's manifest");
    writeFileSync(join(dir, "package.json"), JSON.stringify(change(manifest)));
    for (const module of ["dist/ast/is.js", "dist/ast/is.generated.js"]) {
      const text = readFileSync(join(dir, module), "utf8");
      assert.ok(text.includes('import { SyntaxKind } from "#enums/syntaxKind";'), `${module} imports SyntaxKind`);
      writeFileSync(join(dir, module), text.replace('import { SyntaxKind } from "#enums/syntaxKind";', line));
    }
    return dir;
  };
  // The real path of what Node loads for `specifier` from a module of the
  // copy, or null where resolving or loading it throws.
  const nodeResolves = (dir: string, specifier: string): string | null => {
    writeFileSync(join(dir, "probe.mjs"),
      `await import(${JSON.stringify(specifier)});\nconsole.log(import.meta.resolve(${JSON.stringify(specifier)}));\n`);
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
    ["a specifier ending /", "#enums/syntaxKind/", false, imports({ "#enums/syntaxKind/": "./dist/enums/syntaxKind.js" }),
      'import { SyntaxKind } from "#enums/syntaxKind/";'],
    ["a specifier with a .. segment", "#enums/../enums/syntaxKind", false, (m) => m,
      'import { SyntaxKind } from "#enums/../enums/syntaxKind";'],
    ["an import of a name the module does not export", point, false, (m) => m,
      'import { MissingExport as SyntaxKind } from "#enums/syntaxKind";'],
    ["an import with JSON attributes", point, false, (m) => m,
      'import { SyntaxKind } from "#enums/syntaxKind" with { type: "json" };'],
  ];
  for (const [what, specifier, expected, change, line] of variants) {
    const dir = copy(change, line);
    const reviewed = specifier === point ? compilerApiGuards.entryModule : "dist/enums/syntaxKind.js";
    const nodes = nodeResolves(dir, specifier) === realpathSync(join(dir, reviewed));
    assert.equal(nodes, expected, `${what}: Node resolves ${specifier} ${expected ? "to" : "elsewhere than"} ${reviewed}`);
    assert.equal(activeGuards(compilerApiGuards, dir)?.size === compilerApiGuards.guards.length, nodes,
      `${what}: activated exactly where Node resolves the reviewed module`);
  }
  // Each rejected activation must leave the unchecked module unevaluated.
  for (const form of ["manifest redirect", "extra static import", "dynamic import"] as const) {
    const dir = copy(form === "manifest redirect"
      ? imports({ "#enums/syntaxKind": "./dist/effect.js" }) : m => m);
    const marker = join(dir, "marker");
    writeFileSync(join(dir, "dist/effect.js"),
      'import { writeFileSync } from "node:fs";\n' +
      `writeFileSync(${JSON.stringify(marker)}, "ran");\n` +
      'export { SyntaxKind } from "./enums/syntaxKind.js";\n');
    if (form !== "manifest redirect") {
      const path = join(dir, "dist/ast/ast.js");
      writeFileSync(path, readFileSync(path, "utf8") + (form === "extra static import"
        ? '\nimport "../effect.js";\n' : '\nimport("../effect.js");\n'));
    }
    assert.equal(activeGuards(compilerApiGuards, dir), null, `${form}: no table`);
    // Dynamic import's evaluation is asynchronous; give it a turn to run.
    await new Promise<void>(done => setTimeout(done, 50));
    assert.ok(!existsSync(marker), `${form}: unchecked top-level code did not run`);
  }
  console.log("pre-load closure: manifest redirect, extra static import and dynamic import refused; all three markers absent");
  assert.equal(activeGuards({ ...compilerApiGuards, conditions: ["node", "import", "default"] }, root), null,
    "conditions other than the running Node's: no table");
  // Symlink-preserving resolution, by a flag or NODE_OPTIONS, activates no
  // table: Node then gives modules their symlinked paths as parents.
  const activeIn = (args: readonly string[], env: Record<string, string>): string => {
    const code = `import { activeGuards } from ${JSON.stringify(pathToFileURL(join(repository, "tools", "family-activation.mts")).href)};\n` +
      `import { compilerApiGuards } from ${JSON.stringify(pathToFileURL(join(repository, "tools", "compiler-api-guards.mts")).href)};\n` +
      `console.log(activeGuards(compilerApiGuards, ${JSON.stringify(root)})?.size ?? 'none');\n`;
    const ran = spawnSync(process.execPath, [...args, "--input-type=module", "-e", code],
      { encoding: "utf8", env: { ...process.env, ...env } });
    assert.equal(ran.status, 0, ran.stderr);
    return ran.stdout.trim();
  };
  assert.equal(activeIn([], {}), String(compilerApiGuards.guards.length), "a plain process activates the table");
  assert.equal(activeIn(["--preserve-symlinks"], {}), "none", "--preserve-symlinks: no table");
  assert.equal(activeIn([], { NODE_OPTIONS: "--preserve-symlinks-main" }), "none", "NODE_OPTIONS --preserve-symlinks-main: no table");
  // Recognition loads nothing: a client import binds a guard only where
  // Node resolves it to the URL of a module activation loaded. A query names
  // another instance of the same file, whose function Node gives as another
  // (run under Node), and binds none; a file of the installation activation
  // did not load is refused unloaded: its top-level code, which writes a
  // marker, does not run.
  const client = join(root, "client.mjs");
  const generated = "./dist/ast/is.generated.js";
  const bound = importedGuard(client, generated, "isIdentifier");
  assert.ok(bound && "entry" in bound && bound.entry?.name === "isIdentifier", "the loaded module's isIdentifier is the guard");
  assert.equal(importedGuard(client, `${generated}?review`, "isIdentifier"), null, "a query binds no guard");
  assert.equal(importedGuard(client, `${generated}#review`, "isIdentifier"), null, "a fragment binds no guard");
  const instances = spawnSync(process.execPath, ["--input-type=module", "-e",
    `const url = ${JSON.stringify(pathToFileURL(join(realpathSync(root), "dist", "ast", "is.generated.js")).href)};\n` +
    "const a = await import(url), b = await import(url + '?review');\nconsole.log(a.isIdentifier !== b.isIdentifier);\n"],
    { encoding: "utf8" });
  assert.equal(instances.stdout.trim(), "true", `Node loads another isIdentifier with a query: ${instances.stderr}`);
  // A copy of the package installed in another project, activated by the
  // compiler API's description naming that installation; its declarations
  // are the reviewed ones.
  const project = runDirectory("tscert-guard-effect-");
  const effected = join(project, "node_modules", hostPackage.name);
  mkdirSync(join(project, "node_modules"));
  cpSync(root, effected, { recursive: true, dereference: true });
  writeFileSync(join(effected, "dist", "effect.js"), 'import { writeFileSync } from "node:fs";\n' +
    'writeFileSync(new URL("./marker", import.meta.url), "ran");\nexport function isIdentifier(node) {\n    return true;\n}\n');
  useFamiliesForTests([{ ...compilerApiFamily, installation: { ...compilerApiFamily.installation, from: project } }]);
  try {
    assert.equal(importedGuard(join(effected, "client.mjs"), "./dist/effect.js", "isIdentifier"), null,
      "an installation file activation did not load binds no guard");
    assert.ok(!existsSync(join(effected, "dist", "marker")), "its top-level code did not run");
    const stood = importedGuard(join(effected, "client.mjs"), generated, "isIdentifier");
    assert.ok(stood && "entry" in stood && stood.entry?.name === "isIdentifier", "the stand-in's loaded module binds");
  } finally {
    useFamiliesForTests(null);
  }
  console.log(`activation: the reviewed table resolves, every entry; ${mismatches.length} tables differing from the installation in one recorded fact each, and a table of other conditions than the running Node's, are none, as is every table under symlink-preserving resolution; over ${variants.length} changed copies of the package, activated exactly where Node loads the reviewed module; recognition binds a loaded module's export, and neither a query, a fragment nor an unloaded file, whose code does not run`);
}
