// The compiler-API contract (COMPILER-API.md, "Binding the contract to the
// implementation") checked against the installed package, without a build.
//
// C0, binding: the host package is the installation the front end resolves,
// its declarations' digest the reviewed one; another package naming the host
// in its manifest is no host.
//
// C1, enums: for every host enum the contract reads (`hostEnums` in
// tools/compiler-api.mts), each member of its `.enum.d.ts` is a plain integer
// literal equal to the value of the runtime object Node loads for
// `#enums/<file>` under the `default` condition, the runtime object's own keys are
// exactly the members and their reverse mappings, data properties, each
// reverse key holding the name of a member with its value, and the entry points that
// export the enum export that object.
//
// C4, node lists: every transparent row of a node list answers as a dense
// readonly array's, through throwing and re-entrant callbacks and iterators
// left early or interleaved.
//
// C5, open reads: at each key the front end reads a compiler-provided object
// at through an open read (`%Read:k%`), the lookup along the object's chain
// finds a data property, or the audited `kind` getter of a node's base
// prototype (SOURCE-CONTRACTS.md, "Open reads").
//
// C4, allocating members: each member the contract refuses as allocating is
// declared as reviewed, and under Node two reads of it give different values
// where a stable member gives one.
import assert from "node:assert/strict";
import { copyFileSync, cpSync, mkdirSync, readdirSync, readFileSync, symlinkSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { auditedSyncMethods, compilerApiFamily, hostNodeListMembers, hostViews, hostEnums, hostPackage, statedGuards } from "../tools/compiler-api.mts";
import { declarationsDigest, enumObjectMatches, installationRoot, isHostFile, reviewedFamilies, useFamiliesForTests } from "../tools/family-activation.mts";
import { stringFamily } from "../pipeline/string-family.mts";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { runDirectory } from "../pipeline/run-directory.mts";
import { openCompiler, releaseCompiler } from "../tools/compiler-channel.mts";
import { fieldOf } from "../tools/thrown.mts";
import { sync as syncApi, syntax } from "../tools/syntax.mts";

// The package the front end resolves, from tools/.
const root = dirname(createRequire(resolve(import.meta.dirname, "../tools/package.json"))
  .resolve(`${hostPackage.name}/package.json`));
assert.equal(installationRoot(compilerApiFamily), root, "the description's installation is the package the tools resolve");
const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
assert.ok(typeof manifest === "object" && manifest !== null, "the host package's manifest is an object");
assert.ok("name" in manifest && manifest.name === hostPackage.name && "version" in manifest &&
  manifest.version === hostPackage.version,
  `the installed host package is ${hostPackage.name} ${hostPackage.version}`);
assert.ok(isHostFile(join(root, "dist", "ast", "index.d.ts")), "the package's declarations are host files");
// C0, binding: every reviewed description's installation has the
// description's digest, and a package elsewhere whose manifest names the
// host package is no host.
for (const description of reviewedFamilies)
  assert.equal(declarationsDigest(installationRoot(description)), description.installation.digest,
    `the family ${description.marker}'s declarations are the reviewed ones`);
const lookalike = resolve(import.meta.dirname, "../pipeline/host-fixture/ast.d.ts");
assert.ok(!isHostFile(lookalike), "a lookalike package with the host's manifest is no host");
// Activation fails closed (HOST-FAMILIES.md, "Activation"): a description
// whose digest, version or installation differs from the package Node
// resolves refuses every read of the package's declarations, each beside the
// reviewed description, under which the same file is a host file.
{
  const file = join(root, "dist", "ast", "index.d.ts");
  const refusedUnder = (description: typeof compilerApiFamily, at: string, refusal: RegExp, what: string): void => {
    useFamiliesForTests([description]);
    try {
      assert.throws(() => isHostFile(at), refusal, what);
    } finally {
      useFamiliesForTests(null);
    }
  };
  refusedUnder({ ...compilerApiFamily, installation: { ...compilerApiFamily.installation, digest: "0".repeat(64) } }, file,
    /is not the one the family RemoteNode was reviewed against: its declarations' digest is/, "another digest");
  refusedUnder({ ...compilerApiFamily, package: { ...compilerApiFamily.package, version: "7.0.1" } }, file,
    /is not the family RemoteNode's typescript 7.0.1: its manifest names typescript 7.0.2/, "another version");
  // The package of the same name and version Node finds from the stand-in's
  // project (`pipeline/fixture-links.mts`), whose declarations differ.
  refusedUnder({ ...compilerApiFamily, installation: { ...compilerApiFamily.installation, from: "pipeline/host-fixture-project" } },
    lookalike, /is not the one the family RemoteNode was reviewed against/, "another installation of the package's name");
  refusedUnder({ ...compilerApiFamily, installation: { ...compilerApiFamily.installation, from: "docs" } }, file,
    /the family RemoteNode's package typescript does not resolve from docs/, "an installation Node does not find");
  useFamiliesForTests([compilerApiFamily]);
  try {
    assert.ok(isHostFile(file), "the reviewed description, the one thing changed");
  } finally {
    useFamiliesForTests(null);
  }
  // Ownership is the inventory the digest covers: in a copy of the
  // string-tagged stand-in, linked into a project as Node finds it, a
  // dependency's declaration in a nested `node_modules` and a declaration
  // reached through a symbolic link inside the package are no host files,
  // and leave the digest unchanged; the package's own declarations are, by
  // their real paths through the link; a declaration of an arbitrary
  // extension refuses the installation.
  const project = runDirectory("tscert-inventory-");
  const copy = join(project, "package");
  cpSync(resolve(import.meta.dirname, "../pipeline/string-family-fixture"), copy, { recursive: true });
  mkdirSync(join(copy, "node_modules", "dep"), { recursive: true });
  writeFileSync(join(copy, "node_modules", "dep", "index.d.ts"), "export interface Unit { readonly type: string; }\n");
  writeFileSync(join(project, "outside.d.ts"), "export interface Unit { readonly type: string; }\n");
  symlinkSync(join(project, "outside.d.ts"), join(copy, "linked.d.ts"));
  mkdirSync(join(project, "node_modules"));
  symlinkSync(copy, join(project, "node_modules", stringFamily.package.name));
  const copied = { ...stringFamily, installation: { ...stringFamily.installation, from: project } };
  useFamiliesForTests([compilerApiFamily, copied]);
  try {
    assert.ok(isHostFile(join(project, "node_modules", stringFamily.package.name, "ast.d.ts")), "the package's own declaration, through the link");
    assert.ok(!isHostFile(join(copy, "node_modules", "dep", "index.d.ts")), "a nested dependency's declaration is no host file");
    assert.ok(!isHostFile(join(copy, "linked.d.ts")), "a declaration reached through a symbolic link is no host file");
  } finally {
    useFamiliesForTests(null);
  }
  // Two active descriptions own no guard entry together, so a guard's
  // family is its entry's.
  useFamiliesForTests([stringFamily, { ...copied, marker: "StringFixtureCopy" }]);
  try {
    assert.throws(() => isHostFile(join(copy, "ast.d.ts")), /the families StringFixture and StringFixtureCopy share a guard entry/);
  } finally {
    useFamiliesForTests(null);
  }
  const extended = runDirectory("tscert-inventory-extension-");
  cpSync(resolve(import.meta.dirname, "../pipeline/string-family-fixture"), join(extended, "node_modules", stringFamily.package.name),
    { recursive: true });
  writeFileSync(join(extended, "node_modules", stringFamily.package.name, "styles.d.css.ts"), "declare const styles: string;\nexport default styles;\n");
  refusedUnder({ ...stringFamily, installation: { ...stringFamily.installation, from: extended } },
    join(extended, "node_modules", stringFamily.package.name, "ast.d.ts"),
    /a declaration of an arbitrary extension, which no reading rule covers/, "an arbitrary-extension declaration");
  console.log("C0: each reviewed description's installation has its digest; a description of another digest, version or installation, or one whose installation Node does not find, refuses the package's declarations; a nested dependency's declaration and one reached through a symbolic link are no host files; an arbitrary-extension declaration refuses the installation");
}

// `#enums/*` under the `default` condition, as the manifest's `imports` map
// states it.
const imports = "imports" in manifest && typeof manifest.imports === "object" && manifest.imports !== null &&
  "#enums/*" in manifest.imports ? manifest.imports["#enums/*"] : undefined;
const target = typeof imports === "object" && imports !== null && "default" in imports &&
  typeof imports.default === "string" ? imports.default : undefined;
const types = typeof imports === "object" && imports !== null && "types" in imports &&
  typeof imports.types === "string" ? imports.types : undefined;
assert.ok(target && types, "the manifest maps #enums/* to a declaration and a runtime file");

// The entry points, as the manifest's `exports` map resolves them.
const exportEntries: [string, unknown][] = Object.entries("exports" in manifest && typeof manifest.exports === "object" &&
  manifest.exports !== null ? manifest.exports : {});
const exportsMap = new Map(exportEntries);
/** A module namespace object, read by key. */
const isNamespace = (value: unknown): value is Record<string, unknown> => typeof value === "object" && value !== null;
const entryPoint = async (path: string): Promise<Record<string, unknown>> => {
  const file = exportsMap.get(path);
  assert.ok(typeof file === "string", `the manifest exports ${path}`);
  const module: unknown = await import(pathToFileURL(join(root, file)).href);
  assert.ok(isNamespace(module), `${path}: a module namespace`);
  return module;
};
const ast = await entryPoint("./unstable/ast");
const sync = await entryPoint("./unstable/sync");
let members: number = 0;
for (const { name, file } of hostEnums) {
  const declaration = readFileSync(join(root, types.replace("*", file)), "utf8");
  const body = /export declare enum (\w+) \{\n([^}]*)\}/.exec(declaration);
  assert.ok(body && body[1] === name, `${file}: one declared enum ${name}`);
  const declared = (body[2] ?? "").split("\n").filter((line) => line.trim()).map((line) => {
    const member = /^\s+(\w+) = (-?\d+),?$/.exec(line);
    assert.ok(member, `${name}: a member that is no integer literal: ${line}`);
    return { member: member[1] ?? "", value: Number(member[2]) };
  });
  const module: unknown = await import(pathToFileURL(join(root, target.replace("*", file))).href);
  assert.ok(isNamespace(module), `${name}: a module namespace`);
  const runtime = module[name];
  assert.ok(typeof runtime === "object" && runtime !== null, `${name}: the runtime module exports an object`);
  const runtimeEntries: [string, unknown][] = Object.entries(runtime);
  const values = new Map(runtimeEntries);
  for (const { member, value } of declared)
    assert.equal(values.get(member), value, `${name}.${member}: declared ${value}, at run time ${values.get(member)}`);
  // The runtime object is the emitted enum object (`emitted-enum`): each
  // member an own data property holding its value, at each value's key an
  // own data property holding the name of a member with that value, and no
  // other own key, so a read of a key runs no code. The object is mutable;
  // that it is never written is F5.
  assert.ok(enumObjectMatches(runtime, declared.map(({ member, value }) => ({ name: member, value }))),
    `${name}: the runtime object's own keys are its members and reverse mappings, data properties`);
  for (const exported of [ast, sync])
    if (name in exported) assert.equal(exported[name], runtime, `${name}: an entry point exports the object #enums loads`);
  members += declared.length;
}
console.log(`C1: ${hostEnums.length} host enums, ${members} members, each the runtime value, with its reverse mapping, own data properties`);

// C4 for node lists (COMPILER-API.md, "Node lists"; T4): on lists of lengths
// around 16, where index getters move from the prototype to the instance,
// each transparent row gives the dense readonly array's answer, with
// callbacks recording their arguments, throwing, re-entering and iterators
// interleaved or left early; afterwards every row answers as at the start.
// Each own member the contract states (`hostNodeListMembers`) is declared
// as reviewed by its owner, and under Node is backed as stated: `pos` and
// `end` by getters of the list's prototype chain, without setters, each
// giving one integer; `hasTrailingComma` and `transformFlags` by own data
// properties holding `undefined` and 0, before and after every row runs; in
// the package's JavaScript only `RemoteNodeList` names those two fields.
{
  const declarations = readFileSync(join(root, "dist", "ast", "ast.d.ts"), "utf8");
  for (const { name, owner, text } of hostNodeListMembers) {
    const start = declarations.indexOf(`export interface ${owner}`);
    const body = start < 0 ? "" : declarations.slice(start, declarations.indexOf("\n}", start));
    assert.equal(body.split("\n").filter(line => line.trim() === text).length, 1,
      `the node list member ${name} is declared by ${owner} as reviewed: ${text}`);
  }
  const generated = readFileSync(join(root, "dist", "api", "node", "node.generated.js"), "utf8");
  const classStart = generated.indexOf("export class RemoteNodeList extends Array {");
  const classBody = generated.slice(classStart, generated.indexOf("\n}\n", classStart));
  assert.ok(classStart >= 0 && /^ {4}hasTrailingComma;$/m.test(classBody) && /^ {4}transformFlags = 0;$/m.test(classBody),
    "RemoteNodeList declares hasTrailingComma uninitialized and transformFlags at 0");
  const files = (dir: string): string[] => readdirSync(dir, { withFileTypes: true }).flatMap(entry =>
    entry.isDirectory() ? files(join(dir, entry.name)) : entry.name.endsWith(".js") ? [join(dir, entry.name)] : []);
  for (const file of files(join(root, "dist"))) {
    const text = readFileSync(file, "utf8");
    const outside = file.endsWith(join("api", "node", "node.generated.js"))
      ? text.slice(0, classStart) + text.slice(classStart + classBody.length) : text;
    assert.ok(!/hasTrailingComma|transformFlags/.test(outside), `${file} names no node list field outside RemoteNodeList`);
  }
}
const nodeListMembersHold = (list: object, what: string): void => {
  for (const { name, backing, contract } of hostNodeListMembers) {
    const own = Object.getOwnPropertyDescriptor(list, name);
    if (backing === "getter") {
      // The first link of the list's prototype chain owning the key holds a
      // getter without a setter.
      const getter = (proto: unknown): boolean => {
        if (typeof proto !== "object" || proto === null) return false;
        const found = Object.getOwnPropertyDescriptor(proto, name);
        return found ? found.get !== undefined && found.set === undefined : getter(Object.getPrototypeOf(proto));
      };
      assert.ok(own === undefined && getter(Object.getPrototypeOf(list)),
        `${what}: ${name} is a prototype getter without setter`);
    } else
      assert.ok(own !== undefined && "value" in own && own.get === undefined && own.set === undefined,
        `${what}: ${name} is an own data property`);
    const value: unknown = Reflect.get(list, name);
    assert.equal(Reflect.get(list, name), value, `${what}: two reads of ${name} give one value`);
    assert.ok(contract === "number" ? typeof value === "number" && Number.isInteger(value)
      : value === undefined || typeof value === "boolean", `${what}: ${name} meets ${contract}: ${String(value)}`);
    if (backing === "field") assert.equal(value, contract === "number" ? 0 : undefined, `${what}: ${name} as the constructor leaves it`);
  }
};
{
  const dir = runDirectory("tscert-nodelist-");
  for (const n of [0, 1, 15, 16, 17, 32]) {
    const source = Array.from({ length: n }, (_, i) => `export const v${i} = ${i};\n`).join("");
    const file = join(dir, `list${n}.ts`);
    writeFileSync(file, source);
    const list = openText(file, source).statements;
    const what = `a node list of length ${n}`;
    // The elements as indexed reads give them, before anything else runs.
    const elements: unknown[] = [];
    for (let i = 0; i < list.length; i++) elements.push(list[i]);
    const metadata = hostNodeListMembers.map(m => Reflect.get(list, m.name));
    const rows = (): void => {
      assert.equal(list.length, n, `${what}: length`);
      nodeListMembersHold(list, what);
      assert.deepEqual(hostNodeListMembers.map(m => Reflect.get(list, m.name)), metadata, `${what}: its members as at the start`);
      const isArray: boolean = Array.isArray(list);
      assert.ok(isArray && typeof list === "object", `${what}: an array object`);
      elements.forEach((e, i) => assert.equal(list[i], e, `${what}: index ${i}`));
      assert.equal(list[n], undefined, `${what}: past the end`);
      assert.equal(Reflect.get(list, "0.5"), undefined, `${what}: a non-integer index`);
      // Every other numeric key, `length - 1` of an empty list among them.
      for (const key of [-1, -0.5, n + 1, 2 ** 32, 2 ** 53, NaN, Infinity, -Infinity])
        assert.equal(list[key], undefined, `${what}: the numeric key ${key}`);
      assert.equal(list[-0], elements[0], `${what}: -0 names the index 0`);
      assert.deepEqual([...list], elements, `${what}: spread`);
      const seen: unknown[] = [];
      for (const x of list) seen.push(x);
      assert.deepEqual(seen, elements, `${what}: for…of`);
      // Every callback member: its arguments and `this`, in order, for each
      // element, the callback answering so that no member stops early.
      const marker = { marker: true };
      const expected = elements.map((e, i) => [marker, e, i, list]);
      const traced = (member: string, run: (f: (this: unknown, x: unknown, i: number, l: unknown) => boolean) => unknown,
          answer: boolean): unknown => {
        const trace: unknown[][] = [];
        const result = run(function (this: unknown, x, i, l) { trace.push([this, x, i, l]); return answer; });
        assert.deepEqual(trace, expected, `${what}: ${member}'s this and arguments in order`);
        return result;
      };
      traced("forEach", f => list.forEach(f, marker), false);
      assert.equal(traced("some", f => list.some(f, marker), false), false, `${what}: some`);
      assert.equal(traced("every", f => list.every(f, marker), true), true, `${what}: every`);
      assert.equal(traced("find", f => list.find(f, marker), false), undefined, `${what}: find`);
      assert.equal(traced("findIndex", f => list.findIndex(f, marker), false), -1, `${what}: findIndex`);
      assert.deepEqual(traced("map", f => list.map(f, marker), true), elements.map(() => true), `${what}: map`);
      assert.deepEqual(traced("filter", f => list.filter(f, marker), true), elements, `${what}: filter`);
      assert.deepEqual(traced("flatMap", f => list.flatMap(f, marker), true), elements.map(() => true), `${what}: flatMap`);
      assert.equal(list.find((_, i) => i === n - 1), elements[n - 1], `${what}: find`);
      assert.equal(list.findIndex((_, i) => i === n - 1), n - 1, `${what}: findIndex`);
      if (n) assert.equal(list.indexOf(list[n - 1]!), n - 1, `${what}: indexOf`); // asserted: n > 0
      for (const fresh of [list.map(x => x), list.filter(() => true), list.flatMap(x => [x]), list.slice()]) {
        const arrayPrototype: unknown = Array.prototype;
        assert.equal(Object.getPrototypeOf(fresh), arrayPrototype, `${what}: a fresh ordinary array`);
        assert.deepEqual(fresh, elements, `${what}: a fresh array of the elements`);
      }
      assert.equal(list.at(0.5), undefined, `${what}: at of a non-integer, within T | undefined`);
      if (n) assert.equal(list.at(0), elements[0], `${what}: at`);
      assert.deepEqual([...new Set(list)], elements, `${what}: new Set`);
      const collect = (...xs: unknown[]): unknown[] => xs;
      assert.deepEqual(Reflect.apply(collect, null, list), elements, `${what}: apply of the list itself`);
      assert.deepEqual(collect(...list), elements, `${what}: argument spread`);
      const [first, ...rest] = list;
      assert.deepEqual([first, ...rest].slice(0, n), elements, `${what}: destructuring with a rest`);
      if (!n) assert.equal(list.join(), "", `${what}: join of an empty list`);
    };
    rows();
    // After each interruption, indexed reads and a fresh iteration at once,
    // before anything else could repair the list's state.
    const intact = (after: string): void => {
      elements.forEach((e, i) => assert.equal(list[i], e, `${what}: index ${i} after ${after}`));
      assert.deepEqual([...list], elements, `${what}: a fresh iteration after ${after}`);
    };
    // A callback throwing at each index, of every callback member.
    for (let at = 0; at < n; at++) {
      const stop = (_: unknown, i: number): boolean => { if (i === at) throw Error("stop"); return false; };
      for (const [member, run] of [["forEach", () => list.forEach(stop)], ["some", () => list.some(stop)],
          ["every", () => list.every((x, i) => !stop(x, i))], ["find", () => list.find(stop)],
          ["findIndex", () => list.findIndex(stop)], ["map", () => list.map(stop)],
          ["filter", () => list.filter(stop)], ["flatMap", () => list.flatMap(stop)]] as const) {
        assert.throws(run, /stop/, `${what}: ${member} propagates the callback's exception`);
        intact(`${member} thrown at ${at}`);
      }
    }
    // Iterations left early: by break, by return, by a shorter destructuring.
    for (const _ of list) break;
    intact("a break");
    (() => { for (const _ of list) return; })();
    intact("a return");
    const [_a, _b] = list;
    intact("a shorter destructuring");
    // Re-entrancy: each row run inside callbacks and an iteration of the same
    // list, the outer traversal's results checked too.
    const outer: unknown[] = [];
    list.forEach(x => { rows(); outer.push(x); });
    assert.deepEqual(outer, elements, `${what}: forEach around re-entrant rows`);
    assert.deepEqual(list.map(x => { rows(); return x; }), elements, `${what}: map around re-entrant rows`);
    const iterated: unknown[] = [];
    for (const x of list) { rows(); iterated.push(x); }
    assert.deepEqual(iterated, elements, `${what}: for…of around re-entrant rows`);
    // Two iterators advanced alternately, with reads between their steps.
    const one = list[Symbol.iterator](), two = list[Symbol.iterator]();
    for (let i = 0; i < n; i++) {
      assert.equal(one.next().value, elements[i]);
      assert.equal(list.length, n);
      assert.equal(two.next().value, elements[i]);
      assert.equal(list[n - 1 - i], elements[n - 1 - i]);
    }
    // Writes are refused: an index has a getter and no setter.
    assert.equal(Reflect.set(list, 0, null), false, `${what}: an index write is refused`);
    assert.equal(list[0], elements[0], `${what}: the index unchanged`);
    rows();
  }
  console.log(`C4: node lists of lengths 0, 1, 15, 16, 17 and 32 answer every transparent row as dense readonly arrays; their ${hostNodeListMembers.length} own members are backed as stated and keep their values`);
}

// Reading rule 2 under Node: the members declared `any` are the abstract
// bases' brands, and no node of a parsed file owns or inherits one, so each
// reads `undefined`, as its optional reading admits.
{
  const declarations = readFileSync(join(root, "dist", "ast", "ast.d.ts"), "utf8") +
    readFileSync(join(root, "dist", "ast", "ast.generated.d.ts"), "utf8");
  const brands = [...new Set([...declarations.matchAll(/^\s+(?:readonly )?(\w+): any;$/gm)].map(m => m[1]))];
  assert.ok(brands.length > 0 && brands.every(b => /^_\w+Brand$/.test(b) || b === "type"), `the any members: ${brands}`);
  const file = resolve(import.meta.dirname, "compiler-api.mts");
  const tree = openText(file, readFileSync(file, "utf8"));
  let nodes = 0;
  type AstNode = Parameters<Parameters<typeof tree.forEachChild>[0]>[0];
  const visit = (node: AstNode | typeof tree): void => {
    nodes++;
    for (const brand of brands.filter(b => b !== "type")) assert.ok(!(brand in node), `a node owns ${brand}`);
    node.forEachChild(visit);
  };
  visit(tree);
  console.log(`rule 2: ${brands.length} members declared any; none of ${nodes} nodes holds a brand`);
}

// Declaration texts: every member a named view lists (reading rule 4) is
// declared as reviewed by its owner, the class or interface of that name in
// the sync API's declarations of the installation, and by no other part.
{
  let members = 0;
  const owners = new Map<string, string[]>();
  for (const name of ["api.d.ts", "types.d.ts"]) {
    const file = join(root, "dist", "api", "sync", name);
    const text = readFileSync(file, "utf8");
    const tree = openText(file, text);
    for (const statement of tree.statements) {
      const declared = statement as unknown as { name?: { text?: string }; members?: readonly { getText(f: unknown): string }[] }; // asserted: a statement's optional name and members, read as the compiler declares them
      const owner = declared.name?.text;
      if (!owner || !declared.members) continue;
      owners.set(owner, [...(owners.get(owner) ?? []), ...declared.members.map(m => m.getText(tree).trim())]);
    }
  }
  for (const view of hostViews) {
    const declared = owners.get(view.owner);
    assert.ok(declared, `the view ${view.owner} names a class or interface of the installation`);
    for (const { name, text } of view.members) {
      assert.equal(declared.filter(t => t === text).length, 1, `${view.owner}.${name} is declared as reviewed by its owner: ${text}`);
      members++;
    }
  }
  console.log(`views: ${hostViews.length} named views, ${members} members, each declared as reviewed by its owner`);
}

// C4 for the omitted members: each is declared as reviewed; under Node two
// reads of a documented node's `jsDoc` give different arrays, while a stable
// member gives one value, and a parsed file's `tokenCache`, absent, is a
// `Map` after `getTokenAtPosition` at its `=`.
{
  const declarations = readFileSync(join(root, "dist", "ast", "ast.d.ts"), "utf8");
  for (const { owner, member, text } of compilerApiFamily.omitted)
    assert.ok(declarations.includes(text), `${owner}.${member} is declared as reviewed: ${text}`);
  const file = join(runDirectory("tscert-jsdoc-"), "documented.ts");
  const source = "/** The answer. */\nexport const answer = 42;\n";
  writeFileSync(file, source);
  const tree = openText(file, source);
  const [statement] = tree.statements;
  assert.ok(statement, "the documented statement");
  const first = statement.jsDoc;
  const second = statement.jsDoc;
  assert.ok(first && second && first.length === 1, "the statement's documentation");
  assert.notEqual(first, second, "two reads of jsDoc give different arrays");
  assert.equal(statement.parent, statement.parent, "two reads of a stable member give one value");
  // A node's stable members are prototype getters, not own keys: a copy of
  // its own enumerable keys has none of them (COMPILER-API.md, own keys of
  // host objects).
  const copy: Record<string, unknown> = { ...statement };
  assert.ok(!("kind" in copy) && "parent" in copy, "a spread of a node copies parent and no kind");
  const before: unknown = Reflect.get(tree, "tokenCache");
  syntax.getTokenAtPosition(tree, source.indexOf("="));
  const after: unknown = Reflect.get(tree, "tokenCache");
  assert.ok(before === undefined && after instanceof Map, "getTokenAtPosition assigns tokenCache on the file it is given");
  closeParser();
  console.log("C4: jsDoc allocates on each read; tokenCache is assigned by getTokenAtPosition; a stable member is neither");
}

// The residual's correction under Node (HOST-FAMILIES.md, "Residuals"): the
// negative fixture `invalid-compiler-api-residual-parent`, which a unit naming
// `Identifier` and leaving `SourceFile` to its residual writes, returns
// `undefined` on a source file, whose `parent` the runtime leaves absent.
{
  const dir = runDirectory("tscert-residual-");
  mkdirSync(join(dir, "node_modules"));
  symlinkSync(root, join(dir, "node_modules", hostPackage.name));
  const fixture = join(dir, "residual-parent.ts");
  copyFileSync(resolve(import.meta.dirname, "../pipeline/examples/invalid-compiler-api-residual-parent.ts"), fixture);
  const module: unknown = await import(pathToFileURL(fixture).href);
  assert.ok(isNamespace(module) && typeof module.up === "function", "the fixture exports up");
  const file = join(dir, "parsed.ts");
  const source = "export const answer = 42;\n";
  writeFileSync(file, source);
  const tree = openText(file, source);
  assert.equal(tree.parent, undefined, "a source file's parent is absent");
  assert.equal(module.up(tree), undefined, "up returns undefined on a source file");
  closeParser();
  console.log("residual: the fixture's up returns undefined on a source file under Node");
}

// A look-alike under Node: `invalid-compiler-api-closure-offer-lookalike`
// hands its closure over `Node` a program record whose `kind` is an
// identifier's, and the guard's true branch pushes its absent `text`.
{
  const dir = runDirectory("tscert-lookalike-");
  mkdirSync(join(dir, "node_modules"));
  symlinkSync(root, join(dir, "node_modules", hostPackage.name));
  const fixture = join(dir, "lookalike.ts");
  copyFileSync(resolve(import.meta.dirname, "../pipeline/examples/invalid-compiler-api-closure-offer-lookalike.ts"), fixture);
  const module: unknown = await import(pathToFileURL(fixture).href);
  assert.ok(isNamespace(module) && typeof module.wrong === "function", "the fixture exports wrong");
  const syntaxKind: unknown = Reflect.get(ast, "SyntaxKind");
  assert.ok(isNamespace(syntaxKind), "the package exports SyntaxKind");
  const source = "export const value = 1;\n";
  const file = join(dir, "source.ts");
  writeFileSync(file, source);
  const tree = openText(file, source);
  const out: unknown = module.wrong([{
    kind: syntaxKind.Identifier,
    flags: tree.flags,
    parent: tree,
    pos: 0,
    end: source.length,
    forEachChild<T>(_visitor: (node: Parameters<Parameters<typeof tree.forEachChild>[0]>[0]) => T): T | undefined { return undefined; },
    getSourceFile(): typeof tree { return tree; },
    getStart(): number { return 0; },
    getFullStart(): number { return 0; },
    getEnd(): number { return source.length; },
    getWidth(): number { return source.length; },
    getFullWidth(): number { return source.length; },
    getLeadingTriviaWidth(): number { return 0; },
    getFullText(): string { return source; },
    getText(): string { return source; },
  }]);
  closeParser();
  assert.ok(Array.isArray(out) && out.length === 1 && out[0] === undefined,
    "the look-alike's absent text is pushed into the string[]");
  console.log("look-alike: a program record read as an identifier pushes undefined under Node");
}

// The corrections under Node (COMPILER-API.md, "Corrections"): each negative
// fixture `invalid-compiler-api-corrected-*` returns a corrected member at
// the type the declarations state, and on a node of its kind the runtime
// leaves the member absent, so the function returns `undefined`.
{
  const dir = runDirectory("tscert-corrections-");
  mkdirSync(join(dir, "node_modules"));
  symlinkSync(root, join(dir, "node_modules", hostPackage.name));
  const syntaxKind: unknown = Reflect.get(ast, "SyntaxKind");
  assert.ok(isNamespace(syntaxKind), "the package exports SyntaxKind");
  const corrected: [string, string, string][] = [
    ["source-file-parent", "SourceFile", "export const answer = 42;\n"],
    ["property-signature-initializer", "PropertySignature", "interface I { x: number }\n"],
    ["property-assignment-type", "PropertyAssignment", "export const o = { a: 1 };\n"],
    ["shorthand-assignment-type", "ShorthandPropertyAssignment", "const a = 1;\nexport const o = { a };\n"],
    ["export-assignment-type", "ExportAssignment", "export default 1;\n"],
    ["default-clause-expression", "DefaultClause", "declare const x: number;\nswitch (x) { default: }\n"],
    ["template-raw-text", "NoSubstitutionTemplateLiteral", "export const t = `a`;\n"],
    ["template-flags", "NoSubstitutionTemplateLiteral", "export const t = `a`;\n"],
    ["tagged-template-question-dot", "TaggedTemplateExpression", "declare const tag: (s: TemplateStringsArray) => string;\nexport const t = tag`a`;\n"],
    ["template-tag-constraint", "JSDocTemplateTag", "/** @template T */\nexport function same<T>(x: T): T { return x; }\n"],
  ];
  for (const [slug, kindName, source] of corrected) {
    const fixture = join(dir, `${slug}.ts`);
    copyFileSync(resolve(import.meta.dirname, `../pipeline/examples/invalid-compiler-api-corrected-${slug}.ts`), fixture);
    const module: unknown = await import(pathToFileURL(fixture).href);
    assert.ok(isNamespace(module) && typeof module.read === "function", `${slug}: the fixture exports read`);
    const file = join(dir, `${slug}-input.ts`);
    writeFileSync(file, source);
    const tree = openText(file, source);
    const kind: unknown = syntaxKind[kindName];
    type AstNode = Parameters<Parameters<typeof tree.forEachChild>[0]>[0];
    let found: AstNode | typeof tree | undefined = kind === tree.kind ? tree : undefined;
    // JSDoc is no child: each documented node holds its comments apart.
    const visit = (node: AstNode): undefined => {
      if (!found && node.kind === kind) found = node;
      const docs: unknown = Reflect.get(node, "jsDoc");
      if (Array.isArray(docs)) for (const doc of docs.filter((d): d is AstNode => typeof d === "object" && d !== null && "kind" in d)) visit(doc);
      return node.forEachChild(visit);
    };
    tree.forEachChild(visit);
    assert.ok(found, `${slug}: a ${kindName} in ${JSON.stringify(source)}`);
    assert.equal(module.read(found), undefined, `${slug}: read returns undefined on a ${kindName}`);
  }
  closeParser();
  console.log(`corrections: the ${corrected.length} corrected members' fixtures return undefined under Node`);
}

// Stable links under Node (HOST-FAMILIES.md, "Stable links"): where a path's
// first member is a program record's, a call between the test and the read
// may replace it, and the read returns `undefined` where a string is
// promised. Each fixture is called with program objects at the declared
// shapes' members the guard reads: an identifier's `kind`, and another's.
{
  const dir = runDirectory("tscert-stable-");
  mkdirSync(join(dir, "node_modules"));
  symlinkSync(root, join(dir, "node_modules", hostPackage.name));
  const load = async (name: string, exported: string = "nameText"): Promise<(...args: unknown[]) => unknown> => {
    const fixture = join(dir, `${name}.ts`);
    copyFileSync(resolve(import.meta.dirname, `../pipeline/examples/${name}.ts`), fixture);
    const module: unknown = await import(pathToFileURL(fixture).href);
    assert.ok(isNamespace(module), `${name} is a module`);
    const value: unknown = Reflect.get(module, exported);
    const callable = (f: unknown): f is (...args: unknown[]) => unknown => typeof f === "function";
    assert.ok(callable(value), `${name} exports ${exported}`);
    return value;
  };
  const kinds: unknown = Reflect.get(ast, "SyntaxKind");
  assert.ok(isNamespace(kinds), "the package exports SyntaxKind");
  const identifier: unknown = Reflect.get(kinds, "Identifier");
  const computed: unknown = Reflect.get(kinds, "ComputedPropertyName");
  const mixed = await load("invalid-compiler-api-stable-mixed");
  const named: { name: object } = { name: { kind: identifier, text: "a" } };
  assert.equal(mixed(named, () => { named.name = { kind: computed }; }), undefined,
    "invalid-compiler-api-stable-mixed: the call replaces the record's name");
  const record = await load("invalid-compiler-api-stable-record");
  const holder: { node: object } = { node: { name: { kind: identifier, text: "a" } } };
  assert.equal(record(holder, () => { holder.node = { name: { kind: computed } }; }), undefined,
    "invalid-compiler-api-stable-record: the call replaces the holder's node");
  const chain = await load("invalid-compiler-api-entry-path-record");
  const box: { node: object } = { node: { name: { kind: identifier, text: "a" } } };
  assert.equal(chain({ box }, () => { box.node = { name: { kind: computed } }; }), undefined,
    "invalid-compiler-api-entry-path-record: the call replaces the middle member's node");
  const captured = await load("invalid-compiler-api-stable-let");
  assert.equal(captured({ name: { kind: identifier, text: "a" } }, { name: { kind: computed } }), undefined,
    "invalid-compiler-api-stable-let: the callback replaces the let root");
  const cell = await load("invalid-compiler-api-stable-let-cell");
  assert.equal(cell({ name: { kind: identifier, text: "a" } }, { name: { kind: computed } }), undefined,
    "invalid-compiler-api-stable-let-cell: the callback replaces the mutable name");
  // An optional member of a program record and of a look-alike, removed by
  // the call between the test and the read.
  for (const name of ["invalid-compiler-api-stable-optional-record", "invalid-compiler-api-stable-optional-lookalike"]) {
    const initializerOf = await load(name, "initializerOf");
    const declaration: { kind: unknown; initializer?: object } = { kind: identifier, initializer: { kind: identifier } };
    assert.equal(initializerOf(declaration, () => { delete declaration.initializer; }), undefined,
      `${name}: the call removes the optional member`);
  }
  // The node builders (R2): factory, clone and handwritten visitor roots lack the
  // `parent` their shapes require.
  const made = await load("invalid-compiler-api-node-factory", "made");
  assert.equal(made(), undefined, "invalid-compiler-api-node-factory: a factory node has no parent");
  const cloneParent = await load("invalid-compiler-api-node-clone", "cloneParent");
  const declarationSource = "const x = 1;\n";
  const declarationFile = join(dir, "declaration.ts");
  writeFileSync(declarationFile, declarationSource);
  const [variable] = openText(declarationFile, declarationSource).statements;
  const member = (o: unknown, key: string | number): unknown => typeof o === "object" && o !== null ? Reflect.get(o, key) : undefined;
  const first: unknown = member(member(member(variable, "declarationList"), "declarations"), 0);
  assert.ok(first !== undefined && cloneParent(first) === undefined, "invalid-compiler-api-node-clone: a clone's root has no parent");
  copyFileSync(resolve(import.meta.dirname, "../pipeline/examples/compiler-api-node-jsdoc-visitor-reexport.ts"),
    join(dir, "compiler-api-node-jsdoc-visitor-reexport.ts"));
  for (const [suffix, tagName, kindName] of [
    ["", "param", "JSDocParameterTag"],
    ["-namespace", "property", "JSDocPropertyTag"],
    ["-reexport", "param", "JSDocParameterTag"],
  ]) {
    const name = `invalid-compiler-api-node-jsdoc-visitor${suffix}`;
    const visitorParent = await load(name, "visitorParent");
    const source = tagName === "property"
      ? "/** @typedef {Object} Options\n * @property {number} x\n */\nexport {};\n"
      : "/** @param x */\nfunction f(x: number): void {}\n";
    const file = join(dir, `${name}-input.ts`);
    writeFileSync(file, source);
    const tree = openText(file, source);
    type AstNode = Parameters<Parameters<typeof tree.forEachChild>[0]>[0];
    let tag: AstNode | undefined;
    const visit = (node: AstNode): undefined => {
      if (node.kind === member(kinds, kindName ?? "")) tag = node;
      const docs: unknown = Reflect.get(node, "jsDoc");
      if (Array.isArray(docs)) for (const doc of docs.filter((d): d is AstNode => typeof d === "object" && d !== null && "kind" in d)) visit(doc);
      return node.forEachChild(visit);
    };
    tree.forEachChild(visit);
    assert.equal(member(tag, "kind"), member(kinds, kindName ?? ""), `${name}: a parsed ${tagName} tag`);
    assert.ok(member(tag, "parent") !== undefined, `${name}: the parsed tag has a parent`);
    const replacement = member(first, "name");
    assert.equal(member(replacement, "kind"), identifier, `${name}: a parsed replacement identifier`);
    assert.notEqual(replacement, member(tag, "name"), `${name}: the visitor changes the name`);
    assert.equal(visitorParent(tag, replacement), undefined, `${name}: the replacement root has no parent`);
  }
  // The omitted `tokenCache`: absent at the test, a `Map` after the call.
  const cached = await load("invalid-compiler-api-token-cache", "cached");
  const tokenSource = "export const answer = 42;\n";
  const tokenFile = join(dir, "tokens.ts");
  writeFileSync(tokenFile, tokenSource);
  assert.equal(cached(openText(tokenFile, tokenSource), tokenSource.indexOf("=")), 2,
    "invalid-compiler-api-token-cache: absent at the test, present after getTokenAtPosition");
  closeParser();
  console.log("stable links: a record's member, a mixed path's first member, a chain's middle member, a let root, a record's and a look-alike's optional member replaced or removed by the call, each read returns undefined under Node; tokenCache absent, then present; factory, clone and handwritten JSDoc visitor roots' parents undefined");
}

// The guards' fixtures under Node (HOST-FAMILIES.md, "Guard recognition"):
// `invalid-compiler-api-js-alias` returns 345 on a JSDoc `@typedef`, which
// `isTypeAliasDeclaration` accepts; `compiler-api-guard-argument` evaluates
// a guard's argument once; and the write `invalid-compiler-api-enum-record-write`
// makes, which F5 excludes, turns `isIdentifier` false on an identifier;
// `invalid-compiler-api-guard-domain-object`'s program object, outside the
// guard's domain, answers `true`; `invalid-compiler-api-type-node` returns
// an `ExpressionWithTypeArguments`, which `TypeNode` does not declare.
{
  const dir = runDirectory("tscert-guards-");
  mkdirSync(join(dir, "node_modules"));
  symlinkSync(root, join(dir, "node_modules", hostPackage.name));
  const fixture = async (name: string): Promise<Record<string, unknown>> => {
    const copy = join(dir, `${name}.ts`);
    copyFileSync(resolve(import.meta.dirname, `../pipeline/examples/${name}.ts`), copy);
    const module: unknown = await import(pathToFileURL(copy).href);
    assert.ok(isNamespace(module), `${name}: a module`);
    return module;
  };
  type AstNode = Parameters<Parameters<ReturnType<typeof openText>["forEachChild"]>[0]>[0];
  const first = (file: string, source: string, kind: number): AstNode => {
    writeFileSync(file, source);
    const tree = openText(file, source);
    let found: AstNode | undefined;
    const visit = (node: AstNode): undefined => {
      if (!found && node.kind === kind) found = node;
      const docs: unknown = Reflect.get(node, "jsDoc");
      if (Array.isArray(docs)) for (const doc of docs.filter((d): d is AstNode => typeof d === "object" && d !== null && "kind" in d)) visit(doc);
      return node.forEachChild(visit);
    };
    tree.forEachChild(visit);
    assert.ok(found, `a node of kind ${kind} in ${JSON.stringify(source)}`);
    return found;
  };
  const syntaxKind: unknown = Reflect.get(ast, "SyntaxKind");
  assert.ok(isNamespace(syntaxKind), "the package exports SyntaxKind");
  const unary = (v: unknown): v is (x: unknown) => unknown => typeof v === "function";
  const nullary = (v: unknown): v is () => unknown => typeof v === "function";
  const alias = await fixture("invalid-compiler-api-js-alias");
  assert.ok(unary(alias.aliasKind), "the fixture exports aliasKind");
  const typedef = first(join(dir, "typedef.js"), "/** @typedef {string} Name */\nexport {};\n", 345);
  assert.equal(alias.aliasKind(typedef), 345, "aliasKind returns 345 on a @typedef");
  // `blocker-type-alias-guard-member` reads `typeParameters` on both arms
  // of the guard: the audited shape of kind 345 states it.
  const members = await fixture("blocker-type-alias-guard-member");
  assert.ok(unary(members.arity), "the fixture exports arity");
  assert.equal(members.arity(typedef), 0, "arity is 0 on a @typedef without @template");
  const templated = first(join(dir, "templated.js"), "/**\n * @template T, U\n * @typedef {{ a: T, b: U }} Pair\n */\nexport {};\n", 345);
  assert.equal(members.arity(templated), 2, "arity is 2 on a @typedef with two @template tags");
  const argument = await fixture("compiler-api-guard-argument");
  assert.ok(unary(argument.counted), "the fixture exports counted");
  const name = first(join(dir, "name.ts"), "export const x = y;\n", Number(syntaxKind.Identifier));
  assert.equal(argument.counted(name), 1, "the argument is evaluated once");
  const write = await fixture("invalid-compiler-api-enum-record-write");
  assert.ok(nullary(write.rewrite), "the fixture exports rewrite");
  const isIdentifier: unknown = Reflect.get(ast, "isIdentifier");
  assert.ok(unary(isIdentifier), "the package exports isIdentifier");
  const before = syntaxKind.Identifier;
  assert.equal(isIdentifier(name), true, "isIdentifier holds of an identifier");
  try {
    write.rewrite();
    assert.equal(isIdentifier(name), false, "after the write, isIdentifier answers false of an identifier");
  } finally {
    Reflect.set(syntaxKind, "Identifier", before);
  }
  const domain = await fixture("invalid-compiler-api-guard-domain-object");
  assert.ok(nullary(domain.identifier), "the fixture exports identifier");
  assert.equal(domain.identifier(), true, "isIdentifier answers true of a program object holding an identifier's kind");
  const typeNode = await fixture("invalid-compiler-api-type-node");
  assert.ok(unary(typeNode.asTypeNode), "the fixture exports asTypeNode");
  const heritage = first(join(dir, "heritage.ts"), "class A extends B<C> {}\n", 234);
  assert.equal(typeNode.asTypeNode(heritage), heritage, "asTypeNode returns the ExpressionWithTypeArguments");
  // The empty pattern of `const {} = o` has no last element: the read at
  // `length - 1` is `undefined`, returned where an element is promised.
  const nodeListLast = await fixture("invalid-compiler-api-node-list-last");
  assert.ok(unary(nodeListLast.lastElement), "the fixture exports lastElement");
  const emptyPattern = first(join(dir, "empty-pattern.ts"), "const {} = o;\n", Number(syntaxKind.ObjectBindingPattern));
  assert.equal(nodeListLast.lastElement(emptyPattern), undefined, "lastElement returns undefined on an empty pattern");
  // A node list owns `hasTrailingComma` at `undefined`, outside the exact
  // reading of an optional Boolean; its `transformFlags` takes a write.
  const trailingComma = await fixture("invalid-compiler-api-node-list-trailing-comma");
  assert.ok(unary(trailingComma.trailingHeld), "the fixture exports trailingHeld");
  const declared = (): AstNode => first(join(dir, "declared.ts"), "function f(a, b,) {}\n", Number(syntaxKind.FunctionDeclaration));
  assert.equal(trailingComma.trailingHeld(declared()), true, "a node list owns hasTrailingComma holding undefined");
  const flagsWrite = await fixture("invalid-compiler-api-node-list-flags-write");
  assert.ok(unary(flagsWrite.mark), "the fixture exports mark");
  assert.equal(flagsWrite.mark(declared()), 1, "a node list's transformFlags takes the write");
  // Node guards on a `parent` that may be absent (HOST-FAMILIES.md,
  // "Undefined arguments"): each returns where `parent` is present and the
  // guard throws a `TypeError` where it is absent, a source file's; a
  // program object of a parenthesized expression's kind passes the guard; a
  // user guard's `true` and a handler of the throw return the absent
  // `parent`.
  const absent = (() => {
    const file = join(dir, "absent.ts");
    writeFileSync(file, "x;\n");
    return openText(file, "x;\n");
  })();
  const undefinedGuards = await fixture("compiler-api-guard-undefined");
  assert.ok(unary(undefinedGuards.parentNamed), "the fixture exports parentNamed");
  assert.ok(unary(undefinedGuards.caught), "the fixture exports caught");
  assert.ok(unary(undefinedGuards.counted), "the fixture exports counted");
  assert.ok(unary(undefinedGuards.parentKind), "the fixture exports parentKind");
  assert.ok(unary(undefinedGuards.outermost), "the fixture exports outermost");
  assert.equal(undefinedGuards.parentNamed(name), false, "parentNamed returns where parent is present");
  assert.equal(undefinedGuards.counted(name), 1, "the guard's argument is evaluated once");
  assert.equal(typeof undefinedGuards.parentKind(name), "number", "parentKind returns a kind");
  assert.equal(undefinedGuards.outermost(name), name, "outermost returns the node below its parentheses");
  const parentNamed = undefinedGuards.parentNamed;
  assert.throws(() => parentNamed(absent), TypeError, "isIdentifier throws on an absent parent");
  assert.equal(undefinedGuards.caught(absent), false, "the handler returns false");
  assert.ok(unary(undefinedGuards.handlerParent), "the fixture exports handlerParent");
  assert.equal(undefinedGuards.handlerParent(absent), undefined, "handlerParent's handler returns the absent parent");
  const objectGuard = await fixture("invalid-compiler-api-guard-undefined-object");
  assert.ok(nullary(objectGuard.made), "the fixture exports made");
  assert.equal(objectGuard.made(), true, "isParenthesizedExpression answers true of a program object of its kind");
  const userGuard = await fixture("invalid-compiler-api-guard-undefined-user");
  assert.ok(unary(userGuard.parentOf), "the fixture exports parentOf");
  assert.equal(userGuard.parentOf(absent), undefined, "parentOf returns a source file's absent parent");
  const caughtGuard = await fixture("invalid-compiler-api-guard-undefined-catch");
  assert.ok(unary(caughtGuard.handled), "the fixture exports handled");
  assert.equal(caughtGuard.handled(absent), undefined, "handled returns a source file's absent parent");
  // Guards returning a family guard's test under `&&` and `||`: each answers
  // `true` of an identifier, which they promise is a function declaration.
  const binary = (v: unknown): v is (x: unknown, y: unknown) => unknown => typeof v === "function";
  const andPromise = await fixture("invalid-compiler-api-guard-and-promise");
  assert.ok(binary(andPromise.named), "the fixture exports named");
  const kept: unknown = andPromise.named([name], "x");
  assert.ok(Array.isArray(kept) && kept.length === 1 && kept[0] === name,
    "named keeps an identifier as a function declaration");
  const orPromise = await fixture("invalid-compiler-api-guard-or-promise");
  assert.ok(binary(orPromise.isDeclaration), "the fixture exports isDeclaration");
  assert.equal(orPromise.isDeclaration(name, true), true, "isDeclaration answers true of an identifier");
  // Another subpath of a package whose manifest maps it to other code: the
  // guard's declaration in TypeScript, a function answering `true` under
  // Node.
  const other = runDirectory("tscert-guard-subpath-");
  const installed = join(other, "node_modules", hostPackage.name);
  cpSync(root, installed, { recursive: true, dereference: true });
  const otherManifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
  assert.ok(typeof otherManifest === "object" && otherManifest !== null && "exports" in otherManifest &&
    typeof otherManifest.exports === "object" && otherManifest.exports !== null, "the package's exports");
  writeFileSync(join(installed, "package.json"), JSON.stringify({ ...otherManifest,
    exports: { ...otherManifest.exports, "./unstable/other": "./other.js" } }));
  writeFileSync(join(installed, "other.js"), "export function isIdentifier(node) {\n    return true;\n}\n");
  copyFileSync(resolve(import.meta.dirname, "../pipeline/examples/invalid-compiler-api-guard-subpath.ts"),
    join(other, "subpath.ts"));
  const subpath: unknown = await import(pathToFileURL(join(other, "subpath.ts")).href);
  assert.ok(isNamespace(subpath) && unary(subpath.name), "the fixture exports name");
  const statement = first(join(dir, "statement.ts"), "x;\n", Number(syntaxKind.ExpressionStatement));
  assert.equal(subpath.name(statement), undefined, "name returns undefined on an expression statement");
  // A re-export TypeScript reads at the guard, whose `.js` Node loads instead.
  for (const file of ["compiler-api-guard-mismatch-reexport.js", "invalid-compiler-api-guard-reexport-mismatch.ts"])
    copyFileSync(resolve(import.meta.dirname, `../pipeline/examples/${file}`), join(other, file));
  const mismatch: unknown = await import(pathToFileURL(join(other, "invalid-compiler-api-guard-reexport-mismatch.ts")).href);
  assert.ok(isNamespace(mismatch) && unary(mismatch.name), "the fixture exports name");
  assert.equal(mismatch.name(statement), undefined, "the mismatched re-export reads text of no identifier");
  // Family identity through program code (HOST-FAMILIES.md, "Identity
  // through program code"): a record holding a node passed where a node is
  // expected reads `pos` of no node; a spread's copy of a node has no
  // `kind`; a callback of `forEachChild` asserting its argument an
  // identifier returns the binary expression of `x + 1;`, whose `text` is
  // `undefined`.
  const boxed = await fixture("invalid-compiler-api-boxed-node");
  assert.ok(unary(boxed.boxed), "the fixture exports boxed");
  const anyNode = first(join(dir, "any.ts"), "x;\n", Number(syntaxKind.ExpressionStatement));
  assert.equal(boxed.boxed(anyNode), undefined, "boxed returns undefined");
  const spread = await fixture("invalid-compiler-api-node-spread");
  assert.ok(unary(spread.copiedKind), "the fixture exports copiedKind");
  assert.equal(spread.copiedKind(anyNode), undefined, "a spread's copy has no kind");
  const met = await fixture("invalid-compiler-api-node-intersection-spread");
  assert.ok(unary(met.copiedKind), "the fixture exports copiedKind");
  const identifier = first(join(dir, "identifier.ts"), "x;\n", Number(syntaxKind.Identifier));
  assert.equal(met.copiedKind(identifier), undefined, "a spread's copy of an identifier, a node with a text, has no kind");
  const callback = await fixture("invalid-compiler-api-node-callback-result");
  assert.ok(unary(callback.firstName), "the fixture exports firstName");
  const sum = first(join(dir, "sum.ts"), "x + 1;\n", Number(syntaxKind.ExpressionStatement));
  assert.equal(callback.firstName(sum), undefined, "firstName returns the text of a binary expression");
  // A loop binding's guard (HOST-FAMILIES.md, "A call on an immutable name"):
  // past a nested loop's `continue`, in a `finally`, past a guard excluding
  // another arm, after a write of the binding and past a call replacing a
  // record's node, the element read is a spread, whose `name` is undefined.
  const spreadLiteral = first(join(dir, "spread.ts"), "({ ...a });\n", Number(syntaxKind.ObjectLiteralExpression));
  const named = first(join(dir, "named.ts"), "({ b: 1 });\n", Number(syntaxKind.ObjectLiteralExpression));
  const spreadMember = first(join(dir, "spread-member.ts"), "({ ...a });\n", Number(syntaxKind.SpreadAssignment));
  const propertyMember = first(join(dir, "property-member.ts"), "({ b: 1 });\n", Number(syntaxKind.PropertyAssignment));
  const holdsUndefined = (v: unknown): boolean => Array.isArray(v) && v.length === 1 && v[0] === undefined;
  for (const slug of ["nested-continue", "finally", "partial"]) {
    const loop = await fixture(`invalid-compiler-api-guard-loop-${slug}`);
    assert.ok(unary(loop.names), `${slug}: the fixture exports names`);
    assert.ok(holdsUndefined(loop.names(spreadLiteral)), `${slug}: names reads name of a spread`);
  }
  const written = await fixture("invalid-compiler-api-guard-loop-let");
  assert.ok(binary(written.names), "the fixture exports names");
  assert.ok(holdsUndefined(written.names(named, spreadMember)), "the written binding's name is undefined");
  const record = await fixture("invalid-compiler-api-guard-loop-record");
  assert.ok(binary(record.names), "the fixture exports names");
  const entry = { node: propertyMember };
  assert.ok(holdsUndefined(record.names([entry], () => { entry.node = spreadMember; })),
    "the replaced node's name is undefined");
  closeParser();
  console.log("guards: aliasKind returns 345 on a @typedef and arity its @template count, a guard's argument is evaluated once, a write to SyntaxKind turns isIdentifier false, isIdentifier answers true of a program object, asTypeNode returns a node of kind 234, a subpath mapped to other code and a mismatched re-export read text of no identifier; a boxed node's pos, a spread copy's kind, also of a node met with a record, a callback's asserted identifier's text and an empty pattern's last element are undefined; a node list owns hasTrailingComma holding undefined and its transformFlags takes a write; guards on a parent that may be absent return where it is present and throw a TypeError where it is absent, isParenthesizedExpression answers true of a program object of its kind, and a user guard's true and the throw's handler return the absent parent; guards returning a test under && and || answer true of an identifier; a loop binding read past a nested continue, in a finally, past another arm's guard, after its write or past a call replacing a record's node is a spread");
}

// C5: the compiler-provided objects the front end reads through open reads
// (`privateClient` and `abandon`, `isNode`, `copied`): the API's private
// client at `close`, its process at `kill`, `once`, `exitCode` and
// `signalCode`, and a node at `kind` and `getStart`. Each lookup finds a data
// property, but a node's `kind`, the getter of the package's
// `RemoteNodeBase.prototype`, which reads the node's bytes in the package's encoded tree
// and writes nothing (the family's stable tag, HOST-FAMILIES.md, F2).
{
  type Found = { owner: object; descriptor: { readonly value?: unknown; readonly get?: unknown; readonly set?: unknown } };
  const lookup = (o: object, key: string): Found | undefined => {
    for (let p: unknown = o; typeof p === "object" && p !== null; p = Object.getPrototypeOf(p)) {
      const descriptor = Object.getOwnPropertyDescriptor(p, key);
      if (descriptor) return { owner: p, descriptor };
    }
    return undefined;
  };
  const data = (o: object, key: string, what: string): void => {
    const found = lookup(o, key);
    assert.ok(found && "value" in found.descriptor && !found.descriptor.get && !found.descriptor.set,
      `${what}.${key} is a data property`);
  };
  const dir = runDirectory("tscert-open-read-");
  const api = openCompiler({ cwd: dir });
  try {
    const client = fieldOf(api, "client");
    assert.ok(typeof client === "object" && client !== null, "the API's private client");
    data(client, "close", "API.client");
    const child = fieldOf(fieldOf(client, "channel"), "child");
    assert.ok(typeof child === "object" && child !== null, "the client's process");
    for (const key of ["kill", "once", "exitCode", "signalCode"]) data(child, key, "API.client.channel.child");
  } finally {
    releaseCompiler(api, null);
  }
  const file = join(dir, "open-read.ts");
  const source = "export const answer = 42;\n";
  writeFileSync(file, source);
  const tree = openText(file, source);
  const [statement] = tree.statements;
  assert.ok(statement, "a parsed statement");
  for (const node of [tree, statement]) {
    data(node, "getStart", "a node");
    const kind = lookup(node, "kind");
    assert.ok(kind && kind.descriptor.get && !kind.descriptor.set && !("value" in kind.descriptor) &&
      kind.owner.constructor.name === "RemoteNodeBase", "a node's kind is RemoteNodeBase.prototype's getter");
  }
  closeParser();
  console.log("C5: the open reads of the client, its process and a node find data properties, and a node's kind getter");
}

// C6, stated guards: each stated guard of the sync API is declared as
// reviewed and is, under Node, the reviewed function, `isTypeReference`'s
// helper `isObjectType` among them; `TypeObject`'s prototype defines no
// getter; flags and objectFlags are own data properties; and on a
// program's literal, union, intersection and reference
// types each guard answers `true` on one of them and, answering `true`, leaves
// the members its promise covers at their declared types (T7, regression
// evidence).
{
  const declarations = readFileSync(join(root, "dist", "api", "sync", "api.d.ts"), "utf8");
  const exported = new Map<string, unknown>(Object.entries(sync));
  for (const { name, text, implementation } of statedGuards) {
    assert.equal(declarations.split(text).length, 2, `${name} is declared as reviewed: ${text}`);
    assert.equal(String(exported.get(name)), implementation, `${name} is the reviewed function under Node`);
  }
  assert.equal(String(exported.get("isObjectType")), "function isObjectType(type) {\n    return (type.flags & TypeFlags.Object) !== 0;\n}",
    "isTypeReference's helper isObjectType is the reviewed function under Node");
  const dir = runDirectory("tscert-stated-guards-");
  const file = join(dir, "types.ts");
  writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, target: "es2022", types: [] }, files: ["types.ts"] }));
  writeFileSync(file, [
    `export const s: "s" = "s";`, "export const t: true = true;", "export const f: false = false;",
    "export const n: 1.5 = 1.5;", "export const b: -12n = -12n;", "export const r: Array<string> = [];",
    "export const u: string | undefined = undefined;", "export const i: { a: 1 } & { b: 2 } = { a: 1, b: 2 };",
    "export const m: Map<string, number> = new Map();", ""].join("\n"));
  const api = openCompiler({ cwd: dir });
  let met = 0;
  const exercised = new Set<string>();
  try {
    const project = api.updateSnapshot({ openProjects: [join(dir, "tsconfig.json")] }).getProject(join(dir, "tsconfig.json"));
    const tree = project?.program.getSourceFile(file);
    assert.ok(project && tree, "the stated guards' program");
    for (const statement of tree.statements) {
      const [declaration] = syntax.isVariableStatement(statement) ? statement.declarationList.declarations : [];
      const type: syncApi.Type | undefined = declaration && project.checker.getTypeAtLocation(declaration.name);
      assert.ok(type, "a declared constant's type");
      const prototype: unknown = Object.getPrototypeOf(type);
      assert.ok(typeof prototype === "object" && prototype !== null && prototype.constructor.name === "TypeObject" &&
        Object.values(Object.getOwnPropertyDescriptors(prototype)).every(d => !d.get && !d.set),
        "a checker type is a TypeObject, whose prototype defines no accessor");
      const ownData = (object: object, key: string): unknown => {
        const descriptor = Object.getOwnPropertyDescriptor(object, key);
        assert.ok(descriptor && "value" in descriptor && !descriptor.get && !descriptor.set,
          `${key} is an own data property`);
        return descriptor.value;
      };
      const checkType = (value: syncApi.Type): void => {
        assert.equal(Object.getPrototypeOf(value), prototype, "a registry TypeObject");
        assert.equal(typeof ownData(value, "flags"), "number");
        const objectFlags = ownData(value, "objectFlags");
        assert.ok(typeof objectFlags === "number" || objectFlags === undefined);
        if (syncApi.isObjectType(value)) assert.equal(typeof objectFlags, "number");
      };
      checkType(type);
      const types = (parts: readonly syncApi.Type[]): void => {
        assert.ok(Array.isArray(parts), "getTypes gives an array");
        for (let index = 0; index < parts.length; index++) {
          assert.ok(Object.hasOwn(parts, index), `getTypes has own index ${index}`);
          const part = parts[index];
          assert.ok(part);
          checkType(part);
        }
      };
      if (syncApi.isUnionType(type) || syncApi.isIntersectionType(type)) {
        met++;
        exercised.add(syncApi.isUnionType(type) ? "isUnionType" : "isIntersectionType");
        const first = type.getTypes(), second = type.getTypes();
        types(first);
        types(second);
        assert.notEqual(first, second, "getTypes gives a fresh array of types");
      }
      const guard: string | null = syncApi.isStringLiteralType(type) ? "isStringLiteralType"
        : syncApi.isNumberLiteralType(type) ? "isNumberLiteralType" : syncApi.isBigIntLiteralType(type) ? "isBigIntLiteralType"
        : syncApi.isBooleanLiteralType(type) ? "isBooleanLiteralType" : null;
      const literal: string | null = guard === null ? null : guard.slice(2, -"LiteralType".length).toLowerCase();
      if (guard !== null) {
        met++;
        exercised.add(guard);
        assert.equal(typeof ownData(type, "value"), literal, `a ${literal} literal type's value is a ${literal}`);
        assert.ok(syncApi.isLiteralType(type));
        const seen = new Set<syncApi.FreshableType>();
        const freshable = (value: syncApi.FreshableType | undefined): void => {
          if (value === undefined || seen.has(value)) return;
          seen.add(value);
          checkType(value);
          assert.equal(typeof value.getFreshType, "function");
          assert.equal(typeof value.getRegularType, "function");
          freshable(value.getFreshType());
          freshable(value.getRegularType());
        };
        freshable(type);
      }
      if (syncApi.isTypeReference(type)) {
        met++;
        exercised.add("isTypeReference");
        assert.equal(typeof ownData(type, "objectFlags"), "number");
        checkType(type.getTarget());
      }
    }
  } finally {
    releaseCompiler(api, null);
  }
  assert.equal(met, 9, "every guarded constant meets its guard");
  assert.deepEqual([...exercised].sort(), statedGuards.map(({ name }) => name).sort(),
    "every stated guard answers true on one of the program's types");
  console.log(`C6: ${statedGuards.length} stated guards declared and loaded as reviewed; each answers true and its promised members are at their declared types, on ${met} types`);
}

// C7, symbol tables and type predicates (COMPILER-API.md, "Audits of sync
// members"): `Symbol.getMembers`, `getExports`, the table they build, the
// registry request it makes and `Checker.getTypePredicateOfSignature` are,
// under Node, the audited methods; on a program's class and functions each
// table is a native `Map`, owning no key, shared by every call on its
// symbol, keyed by each value's escaped name, its values the registry's
// symbols, and empty for a symbol with none; a write through another holder
// of the table, of the field caching it or of the registry's map of symbols
// changes what a later call returns; each predicate's `kind` is the
// `TypePredicateKind` member of its form, its name a string exactly for a
// parameter, its index a number, 0 for a predicate about `this` (whose
// declarations state `undefined`), and its type absent exactly for `asserts`
// with no `is` (regression evidence).
{
  const dir = runDirectory("tscert-symbol-tables-");
  const file = join(dir, "subjects.ts");
  writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, target: "es2022", types: [] }, files: ["subjects.ts"] }));
  writeFileSync(file, [
    "export class C {", "  __x = 1;", "  y = 2;", "  static s = 3;",
    "  isC(): this is C { return true; }", "  assertC(): asserts this is C {}", "}",
    "export function tested(x: unknown): x is string { return typeof x === \"string\"; }",
    "export function assertedIs(x: unknown): asserts x is string { if (typeof x !== \"string\") throw Error(); }",
    "export function asserted(x: unknown): asserts x { if (!x) throw Error(); }",
    "export function plain(): void {}", ""].join("\n"));
  const loaded = (owner: object, name: string): string => {
    const method: unknown = Reflect.get(owner, name);
    assert.equal(typeof method, "function", `${name} is a method`);
    return String(method);
  };
  const api = openCompiler({ cwd: dir });
  const kinds = new Set<number>();
  try {
    const project = api.updateSnapshot({ openProjects: [join(dir, "tsconfig.json")] }).getProject(join(dir, "tsconfig.json"));
    const tree = project?.program.getSourceFile(file);
    assert.ok(project && tree, "the symbol tables' program");
    const checker = project.checker;
    const [cls, ...functions] = tree.statements;
    assert.ok(cls && syntax.isClassDeclaration(cls) && cls.name, "the class");
    const owner = checker.getSymbolAtLocation(cls.name);
    assert.ok(owner, "the class's symbol");
    const registry: unknown = Reflect.get(owner, "objectRegistry");
    assert.ok(typeof registry === "object" && registry !== null, "a symbol's registry");
    const registryPrototype: unknown = Object.getPrototypeOf(registry);
    assert.ok(typeof registryPrototype === "object" && registryPrototype !== null, "the registry's prototype");
    const prototypes = { Symbol: syncApi.Symbol.prototype, Checker: syncApi.Checker.prototype,
      SnapshotObjectRegistry: registryPrototype };
    for (const { owner: at, name, implementation } of auditedSyncMethods)
      assert.equal(loaded(prototypes[at], name), implementation, `${at}.${name} is the audited method under Node`);
    const table = (map: ReadonlyMap<string, syncApi.Symbol>, keys: readonly string[]): void => {
      assert.equal(Object.getPrototypeOf(map), Map.prototype, "a table is a native Map");
      assert.equal(Reflect.ownKeys(map).length, 0, "a table owns no key");
      for (const [key, value] of map) {
        assert.equal(typeof key, "string", "a table's key is a string");
        assert.ok(value instanceof syncApi.Symbol, "a table's value is a registry symbol");
        assert.equal(Reflect.get(value, "escapedName"), key, "a table's key is its value's escaped name");
      }
      for (const key of keys) assert.ok(map.has(key), `the table holds ${key}`);
    };
    const members = owner.getMembers(), exports = owner.getExports();
    assert.equal(owner.getMembers(), members, "a symbol's member table is shared by every call");
    assert.equal(owner.getExports(), exports, "a symbol's export table is shared by every call");
    table(members, ["___x", "y", "isC", "assertC"]);
    table(exports, ["s", "prototype"]);
    // Writes through another holder: the table, the field caching it and
    // the registry's own map of symbols are ordinary writable objects, so
    // code holding the symbol changes what a later call returns, a table
    // read and a checker request alike (the assumption T8 states for code
    // outside the verified program). Each write is undone.
    const alias = checker.getSymbolAtLocation(cls.name);
    assert.equal(alias, owner, "the registry gives one symbol per id");
    // Map's own methods, called on the table as code outside the program
    // would, whatever type it reads the table at.
    const standard = new Map<unknown, unknown>();
    const mapSet = standard.set, mapGet = standard.get, mapDelete = standard.delete;
    assert.ok(mapSet === Map.prototype.set && mapGet === Map.prototype.get && mapDelete === Map.prototype.delete);
    const mapCall = (method: "get" | "set" | "delete", map: unknown, key: unknown, value?: unknown): unknown =>
      method === "set" ? mapSet.call(map, key, value) : method === "get" ? mapGet.call(map, key) : mapDelete.call(map, key);
    mapCall("set", members, "forged", 17);
    assert.equal(mapCall("get", owner.getMembers(), "forged"), 17, "a write through another holder of the table is seen");
    mapCall("delete", members, "forged");
    const replaced = new Map<string, number>();
    Reflect.set(owner, "membersCache", replaced);
    assert.equal(owner.getMembers(), replaced, "a replaced cache field is returned");
    Reflect.set(owner, "membersCache", members);
    const symbols: unknown = Reflect.get(registry, "symbols");
    mapCall("set", symbols, owner.id, 17);
    assert.equal(checker.getSymbolAtLocation(cls.name), 17, "a request returns what the registry's map holds");
    mapCall("set", symbols, owner.id, owner);
    const held = [...members.values(), ...exports.values()];
    for (const member of cls.members) {
      const name = syntax.isPropertyDeclaration(member) || syntax.isMethodDeclaration(member) ? member.name : undefined;
      const symbol = name && checker.getSymbolAtLocation(name);
      assert.ok(symbol && held.includes(symbol), "a table's value is the symbol the checker gives at the member");
    }
    const predicates: { at: syncApi.Signature; kind: number | null; named: boolean; type: boolean }[] = [];
    const signatureOf = (node: syntax.Node): syncApi.Signature => {
      const type = checker.getTypeAtLocation(node);
      const [signature] = type ? checker.getSignaturesOfType(type, syncApi.SignatureKind.Call) : [];
      assert.ok(signature, "a call signature");
      return signature;
    };
    const [isC, assertC] = cls.members.filter(m => syntax.isMethodDeclaration(m));
    assert.ok(isC && assertC, "the class's methods");
    predicates.push({ at: signatureOf(isC.name), kind: syncApi.TypePredicateKind.This, named: false, type: true },
      { at: signatureOf(assertC.name), kind: syncApi.TypePredicateKind.AssertsThis, named: false, type: true });
    const expected: [number | null, boolean][] = [[syncApi.TypePredicateKind.Identifier, true],
      [syncApi.TypePredicateKind.AssertsIdentifier, true], [syncApi.TypePredicateKind.AssertsIdentifier, false], [null, false]];
    functions.forEach((statement, i) => {
      const [kind, type] = expected[i] ?? [null, false];
      assert.ok(syntax.isFunctionDeclaration(statement) && statement.name, "a function");
      predicates.push({ at: signatureOf(statement.name), kind, named: kind !== null, type });
      const plain = statement.name.text === "plain";
      assert.equal(plain, kind === null, "only plain states no predicate");
      const symbol = checker.getSymbolAtLocation(statement.name);
      assert.ok(symbol, "a function's symbol");
      if (plain) assert.equal(symbol.getMembers().size, 0, "a symbol with no members has an empty table");
    });
    for (const { at, kind, named, type } of predicates) {
      const predicate = checker.getTypePredicateOfSignature(at);
      if (kind === null) { assert.equal(predicate, undefined, "no predicate"); continue; }
      assert.ok(predicate, "a predicate");
      assert.equal(predicate.kind, kind, `the predicate's kind is ${kind}`);
      kinds.add(predicate.kind);
      // Every predicate has a numeric index, 0 for one about `this`, whose
      // declaration states `undefined`: the views of those state none.
      const index: unknown = Reflect.get(predicate, "parameterIndex");
      assert.ok(typeof index === "number" && (named || index === 0), "an index, 0 for a predicate about this");
      assert.equal(typeof predicate.parameterName === "string", named, "a parameter's name exactly for a parameter");
      assert.equal(predicate.type !== undefined, type, "a type exactly where the predicate states one");
    }
  } finally {
    releaseCompiler(api, null);
  }
  assert.equal(kinds.size, 4, "every TypePredicateKind member is met");
  console.log(`C7: ${auditedSyncMethods.length} sync methods loaded as audited; symbol tables native, shared, keyed by escaped names, written through another holder as the registry is; predicates of ${kinds.size} kinds as declared but a this predicate's index, 0`);
}
