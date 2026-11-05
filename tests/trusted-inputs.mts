// The trusted inputs of the front end, checked without a build: the Node the
// host contracts are audited against, the pinned Node declarations, the file
// TypeScript resolves, imports as TypeScript binds them, and the array
// prototype overlay read from TypeScript's declarations.
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { close as closeParser, parseFile } from "../tools/fragment-parse.mts";
import { collectDeclarations, declarationSpanOf, tsconfigOf } from "../tools/declaration-graph.mts";
import { overlay as arrayOverlay } from "../tools/array-prototype.mts";
import { runDirectory } from "../pipeline/run-directory.mts";
import type { DeclarationDocument } from "../tools/declaration-types.mts";
import type { Ast } from "../tools/fragment.mts";
const pipelineDir = resolve(import.meta.dirname, "../pipeline");
const libraryConfig = tsconfigOf(resolve(pipelineDir, "library-project"));

function must<T>(value: T | null | undefined, message: string): T {
  assert.ok(value !== null && value !== undefined, message);
  return value;
}
/** A TypeScript project of `files`, strict, with `@fixture/NAME` mapped to
 * `NAME.ts`; `graphOf` collects the declaration graph of a client importing
 * from it, `parse` parses such a client. */
function fixtureProject(files: Record<string, string>, lib?: string[]): { graphOf: (text: string) => DeclarationDocument; parse: (text: string) => Ast } {
  const dir = runDirectory("tscert-fixture-project-");
  for (const [name, text] of Object.entries(files)) writeFileSync(join(dir, name), text);
  const config = join(dir, "tsconfig.json");
  writeFileSync(config, JSON.stringify({
    compilerOptions: { strict: true, noEmit: true, module: "Node16", moduleResolution: "Node16", lib,
      paths: Object.fromEntries(Object.keys(files).filter((f) => f.endsWith(".ts") && !f.endsWith(".d.ts"))
        .map((f) => [`@fixture/${f.replace(/\.ts$/, "")}`, [`./${f}`]])) },
    include: ["*.ts"],
  }));
  let clients = 0;
  const client = (text: string) => {
    const file = join(dir, `client-${clients++}.ts`);
    writeFileSync(file, text);
    return file;
  };
  return {
    graphOf: (text: string) => collectDeclarations(client(text), { tsconfigPath: config }),
    parse: (text: string) => parseFile(client(text), false, config),
  };
}

{
  // The host the library contracts are audited against (docs/SOURCE-CONTRACTS.md,
  // "Library modules"): the Node version .nvmrc names runs the suites.
  const pinned = readFileSync(resolve(import.meta.dirname, "../.nvmrc"), "utf8").trim();
  assert.equal(process.version, `v${pinned}`, `run Node ${pinned}, the version .nvmrc names`);
  process.stdout.write(`Node ${pinned}: the version the host contracts are audited against\n`);
}

{
  // Node's declarations the `process` examples read: `@types/node` at the
  // version library-project/package.json pins (`npm ci --prefix pipeline/library-project`).
  // `process` and the members those examples read are declared in these two files.
  const nodeSha = (path: string) =>
    createHash("sha256").update(readFileSync(resolve(pipelineDir, "library-project/node_modules/@types/node", path))).digest("hex");
  const nodeTypes: unknown = JSON.parse(readFileSync(resolve(pipelineDir,
    "library-project/node_modules/@types/node/package.json"), "utf8"));
  assert.ok(nodeTypes && typeof nodeTypes === "object" && "version" in nodeTypes &&
    nodeTypes.version === "22.10.7", "run `npm ci --prefix pipeline/library-project`");
  assert.equal(nodeSha("globals.d.ts"),
    "ba97261afafe85aafe76d988e65e531da8e8cf791c49caf0531f5dd1689bd91b");
  assert.equal(nodeSha("process.d.ts"),
    "42aaa94addeed66a04b61e433c14e829c43d1efd653cf2fda480c5fb3d722ed8");
  process.stdout.write("pinned Node declarations: bytes as reviewed\n");
}

{
  const jsonPath = resolve(pipelineDir, "examples/invalid-collections-json.ts");
  const changedCopy = join(runDirectory("tscert-copy-"), "client.ts");
  writeFileSync(changedCopy, readFileSync(jsonPath, "utf8").replace("value, null", "null, value"));
  assert.throws(() => parseFile(changedCopy, false, libraryConfig, jsonPath),
    /gate:.*TypeScript client source bytes differ/);
  process.stdout.write("a copy other than the file TypeScript resolves: refused\n");
}

{
  const project = fixtureProject({
    "box.ts": "export interface Box { readonly flag: boolean; }\n",
    "barrel.ts": "export type { Box } from './box.js';\n",
    "global.d.ts": "interface GlobalBox { readonly flag: boolean; }\n",
    "other-global.d.ts": "interface GlobalBox { readonly other: number; }\n",
    "labeled.ts": "export interface Box { readonly other: number; }\n",
    "twice.ts": "export * from './box.js';\nexport * from './labeled.js';\n",
    "wrong.ts": "import type { Box } from './box.js';\nexport interface Wrong extends Box { readonly flag: string; }\n",
  });
  const ast = project.parse('import type { Box } from "@fixture/barrel";\n' +
    "export function read(box: Box, global: GlobalBox): boolean { return box.flag && global.flag; }\n");
  const root = must(ast.declarations.roots[0], "the barrel's name");
  assert.equal(root.declaration.module, "./box.ts");
  assert.equal(root.binding.kind === "import" && root.binding.specifier, "@fixture/barrel");
  // A second global declaration merges with the first, as TypeScript merges
  // it: one equation with both declarations' members, identified by the first.
  const global = must(ast.declarations.definitions.find((d) => d.declaration.name === "GlobalBox"), "GlobalBox");
  assert.equal(global.declaration.module, "./global.d.ts");
  assert(global.expression?.k === "object");
  assert.deepEqual(global.expression.fields.map((f) => f.name), ["flag", "other"]);
  // Two star reexports of one name: TypeScript reports TS2308 on the barrel
  // (and would bind the first); the import is refused there.
  assert.throws(() => project.graphOf('import type { Box } from "@fixture/twice";'),
    /TypeScript reports an error in \.\/twice\.ts on the path to Box: .*already exported a member named 'Box'/);
  // An interface TypeScript rejects is not a contract: refused, not interpreted
  // as the empty conjunction of its incompatible fields.
  assert.throws(() => project.graphOf("import type { Wrong } from './wrong.js';"),
    /TypeScript reports an error in \.\/wrong\.ts#Wrong: .*incorrectly extends/);
  process.stdout.write("imports resolved as TypeScript binds them; TypeScript's errors on their path refused\n");
}

{
  // A merged interface's parameter keeps the bound and the default its
  // shorter declaration states, read in that declaration's scope: the
  // definition counts both defaults, and the written application `J` is
  // completed with them and obliged at the bound.
  const project = fixtureProject({});
  const doc = project.parse("interface J<T extends string = \"a\"> { key: T; }\n" +
    "interface J<T, U = boolean> { flag: U; }\n" +
    "export function key(j: J): string { return j.key; }\n").declarations;
  const merged = must(doc.definitions.find((d) => d.declaration.name === "J"), "J");
  assert.deepEqual(merged.parameters.map((p) => [p.name, p.defaulted]), [["T", true], ["U", true]]);
  const written = must(doc.applications.find((a) => a.reference.name === "J"), "the application J");
  assert.deepEqual(written.args.map((a) => a.k), ["literal", "atom"]);
  assert.deepEqual(written.bounds.map((b) => b?.k ?? null), ["atom", null]);
  process.stdout.write("merged interface parameters: bounds and defaults of every declaration\n");
}

{
  // Selecting an empty weak table needs only its own native contract.
  // ES2022 matches the admitted object-key contract; ES2023 adds symbol
  // to WeakKeyTypes, whose multi-key indexed access is outside the fragment.
  const project = fixtureProject({ "base.ts": "export {};" }, ["es2022"]);
  const doc = project.parse("export function table(): WeakMap<object, number> { return new WeakMap<object, number>(); }\n").declarations;
  assert.ok(doc.definitions.some(d => d.declaration.name === "WeakMap"));
  for (const name of ["Map", "Set", "NativeCollectionIterator", "ArrayProto"])
    assert.equal(doc.definitions.some(d => d.declaration.name === name), false, `unneeded ${name}`);
  const plain = project.parse("export function plain(): number { return 1; }\n").declarations;
  assert.equal(plain.definitions.some(d => d.declaration.name === "WeakMap"), false);
}

{
  // An import the overlay of library modules lists is read through it only
  // where TypeScript binds it to Node's declarations: a module the project
  // maps to its own file under Node's name is refused.
  const dir = runDirectory("tscert-fixture-node-name-");
  writeFileSync(join(dir, "fake.ts"), "export function writeFileSync(file: string, data: string): number { return file.length + data.length; }\n");
  writeFileSync(join(dir, "client.ts"), 'import { writeFileSync } from "fs";\n' +
    "export function save(path: string): number { return writeFileSync(path, \"\"); }\n");
  writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
    module: "Node16", moduleResolution: "Node16", types: [], paths: { fs: ["./fake.ts"] } }, include: ["*.ts"] }));
  assert.throws(() => collectDeclarations(join(dir, "client.ts"), { tsconfigPath: join(dir, "tsconfig.json") }),
    (error: unknown) => {
      assert.ok(error instanceof Error);
      assert.match(error.message, /writeFileSync is not a function Node's declarations declare/);
      const span = declarationSpanOf(error);
      assert.ok(span);
      assert.strictEqual(declarationSpanOf(error), span);
      assert.equal("at" in error, false);
      assert.equal(declarationSpanOf(new Error(error.message)), undefined);
      return true;
    });
  process.stdout.write("library modules: an import read through the overlay only from Node's declarations\n");
}

{
  // A string's `split` gives an array, so a source calling one collects the
  // array prototype; a structural `split`, of an object's own member, does
  // not: the receiver's type decides, as for a primitive's prototype.
  const dir = runDirectory("tscert-fixture-split-dependency-");
  const files = {
    structural: "export function f(x: { split(): number }): number { return x.split(); }\n",
    string: "export function g(s: string): number { return s.split(\",\").length; }\n",
  };
  writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true,
    module: "Node16", moduleResolution: "Node16", types: [] }, include: ["*.ts"] }));
  const arrayProtoLoaded = (name: keyof typeof files, receiver: string): boolean => {
    writeFileSync(join(dir, `${name}.ts`), files[name]);
    const at = files[name].indexOf(`${receiver}.split`);
    const doc = collectDeclarations(join(dir, `${name}.ts`), { tsconfigPath: join(dir, "tsconfig.json"),
      memberReceivers: [[at, at + receiver.length]] });
    return doc.definitions.some(d => d.declaration.module === "tscert/array-prototype");
  };
  assert.equal(arrayProtoLoaded("structural", "x"), false, "a structural split loads no array prototype");
  assert.equal(arrayProtoLoaded("string", "s"), true, "a string's split loads the array prototype");
  process.stdout.write("split dependency: a string's split collects the array prototype, a structural one does not\n");
}

{
  const arrays = join(pipelineDir, "examples", "values.ts");
  const doc = collectDeclarations(arrays, { arrays: [0, 0] });
  const proto = doc.definitions.find(d => d.declaration.module === "tscert/array-prototype");
  assert(proto?.expression?.k === "object");
  // A computed key is the symbol it names: `[Symbol.iterator]` is `Symbol.iterator`.
  const keyText = (name: string | { symbol: number }) =>
    typeof name === "string" ? name : `[Symbol.${doc.symbols[name.symbol]?.name}]`;
  const methods = proto.expression.fields.filter(f => !f.optional);
  assert.deepEqual(methods.map(f => keyText(f.name)), arrayOverlay.map(e => e.name));
  const absentHooks = proto.expression.fields.filter(f => f.optional);
  assert.equal(absentHooks.length, 1);
  assert.equal(keyText(must(absentHooks[0], "conversion hook absence").name), "[Symbol.toPrimitive]");
  assert(absentHooks.every(f => f.readonly && f.type.k === "atom" && f.type.name === "undefined"));
  for (const field of methods) {
    const entry = arrayOverlay.find(e => e.name === keyText(field.name));
    // The member's own binders lead; the element binder `T` is last.
    assert(field.readonly && field.type.k === "scheme" && field.type.binders.at(-1)?.name === "T");
    const first = field.type.signatures[0];
    const receiver = first?.k === "function" ? first.receiver : null;
    // An array of a binder, or for `flat`, an array of arrays of one.
    const element = receiver?.k === "array" && receiver.element.k === "array" && entry?.name === "flat"
      ? receiver.element.element : receiver?.k === "array" ? receiver.element : null;
    assert(receiver?.k === "array" && element?.k === "binder");
    assert.equal(receiver.readonly, entry?.from === "ReadonlyArray", `${String(field.name)} receiver`);
  }
  const changed = arrayOverlay.map(e => e.name === "reduce"
    ? { ...e, signature: e.signature.replace("initialValue: U", "initialValue?: U") } : e);
  assert.throws(() => collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: changed }),
    /is not declared as reviewed/);
  const unsound = [{ name: "reduce", from: "ReadonlyArray" as const,
    signature: "reduce(callbackfn: (previousValue: T, currentValue: T, currentIndex: number, array: readonly T[]) => T): T;" }];
  assert.doesNotThrow(() => collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: unsound }),
    "the overlay, not the declaration reader, decides which overloads are trusted");
  // A member the project's library does not declare is absent, not refused.
  const absent = collectDeclarations(arrays, { arrays: [0, 0], arrayOverlay: [
    { name: "notDeclared", from: "ReadonlyArray", signature: "notDeclared(): T;" }] });
  const absentProto = absent.definitions.find(d => d.declaration.module === "tscert/array-prototype");
  assert(absentProto?.expression?.k === "object" && absentProto.expression.fields.length === 0);
  closeParser();
  process.stdout.write("array prototype: overlay members read from TypeScript's declarations\n");
}

{
  // An imported module's document names its binders by the module's
  // identity, not its path: the binder of a bounded application under a
  // generic declaration's scope, and only binders. A literal type and a
  // property key spelling such a name keep it.
  const dir = runDirectory("tscert-binder-names-");
  const spelled = (offset: number) => `T@${join(dir, "mod.ts")}:${offset}`;
  writeFileSync(join(dir, "mod.ts"), `export interface Box<T extends number> {
  value: T;
}
export interface Holder<U extends number> {
  inner: Box<U>;
  "${spelled(1)}": "${spelled(2)}";
}
export function read(h: Holder<number>, tag: "${spelled(3)}"): number {
  return h.inner.value;
}
`);
  writeFileSync(join(dir, "client.ts"), `import { read, type Holder } from "./mod.ts";
export function first(h: Holder<number>): number {
  return read(h, "${spelled(3)}");
}
`);
  const config = join(dir, "tsconfig.json");
  writeFileSync(config, JSON.stringify({ compilerOptions: { strict: true, noEmit: true, module: "Node16",
    moduleResolution: "Node16", allowImportingTsExtensions: true }, include: ["*.ts"] }));
  const ast = parseFile(join(dir, "client.ts"), false, config);
  const module = JSON.stringify(must(ast.modules.find(m => m.location === "./mod.ts"), "the module's document"));
  for (const offset of [1, 2, 3])
    assert.ok(module.includes(JSON.stringify(spelled(offset))), `the spelling ${offset} is kept`);
  assert.equal(module.split(`@${join(dir, "mod.ts")}:`).length - 1, 3, "only the three spellings name the path");
  assert.match(module, /"U@\.\/mod\.ts:\d+"/, "the generic declaration's binder is named by the module's identity");
  closeParser();
  process.stdout.write("imported module binders: named by the module's identity, literal types and keys kept\n");
}

// Carried context retains the declaration identity of erased block types.
{
  const dir = runDirectory("tscert-block-context-");
  const file = join(dir, "client.ts");
  const text = `type A<U> = { v: string };
export function f(): number {
  type A<U> = { v: number };
  const a: A<number> = { v: 1 };
  return a.v;
}
`;
  writeFileSync(file, text);
  writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({
    compilerOptions: { strict: true, noEmit: true }, include: ["*.ts"],
  }));
  try {
    const ast = parseFile(file, true);
    const statement = must(ast.functions[0], "the function").body[0];
    assert.ok(statement?.k === "const", "the erased alias precedes the constant");
    const annotation = must(statement.bindings[0], "the binding").annot;
    assert.ok(annotation?.k === "reference", "the annotation names a declaration");
    const target = must(annotation.reference.target, "the annotation's declaration identity");
    assert.equal(target.span[0], text.indexOf("type A", 1), "the annotation names the block alias");
  } finally {
    closeParser();
  }
  process.stdout.write("carried context: block annotations retain their lexical declaration identity\n");
}
