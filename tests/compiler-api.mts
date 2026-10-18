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
// `#enums/<file>` under the `default` condition, the runtime object's keys are
// exactly the members and their reverse mappings, and the entry points that
// export the enum export that object.
//
// C4, node lists: every transparent row of a node list answers as a dense
// readonly array's, through throwing and re-entrant callbacks and iterators
// left early or interleaved.
//
// C4, allocating members: each member the contract refuses as allocating is
// declared as reviewed, and under Node two reads of it give different values
// where a stable member gives one.
import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { allocatingMembers, hostViews, declarationsDigest, hostDeclarationsDigest, hostEnums, hostPackage, isHostFile } from "../tools/compiler-api.mts";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { runDirectory } from "../pipeline/run-directory.mts";

// The package the front end resolves, from tools/.
const root = dirname(createRequire(resolve(import.meta.dirname, "../tools/package.json"))
  .resolve(`${hostPackage.name}/package.json`));
const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
assert.ok(typeof manifest === "object" && manifest !== null, "the host package's manifest is an object");
assert.ok("name" in manifest && manifest.name === hostPackage.name && "version" in manifest &&
  manifest.version === hostPackage.version,
  `the installed host package is ${hostPackage.name} ${hostPackage.version}`);
assert.ok(isHostFile(join(root, "dist", "ast", "index.d.ts")), "the package's declarations are host files");
// C0, binding: the installed declarations have the reviewed digest, and a
// package elsewhere whose manifest names the host package is no host.
assert.equal(declarationsDigest(root), hostDeclarationsDigest, "the host declarations are the reviewed ones");
const lookalike = resolve(import.meta.dirname, "../pipeline/host-fixture/ast.d.ts");
assert.ok(!isHostFile(lookalike), "a lookalike package with the host's manifest is no host");

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
let members = 0;
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
  // The runtime object's keys: the members, and for each numeric value the
  // reverse mapping to the last member declaring it.
  const expected = new Set(declared.map((d) => d.member));
  for (const { value } of declared) expected.add(String(value));
  assert.deepEqual(new Set(values.keys()), expected, `${name}: the runtime object's keys are its members and reverse mappings`);
  for (const exported of [ast, sync])
    if (name in exported) assert.equal(exported[name], runtime, `${name}: an entry point exports the object #enums loads`);
  members += declared.length;
}
console.log(`C1: ${hostEnums.length} host enums, ${members} members, each the runtime value`);

// C4 for node lists (COMPILER-API.md, "Node lists"; T4): on lists of lengths
// around 16, where index getters move from the prototype to the instance,
// each transparent row gives the dense readonly array's answer, with
// callbacks recording their arguments, throwing, re-entering and iterators
// interleaved or left early; afterwards every row answers as at the start.
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
    const rows = (): void => {
      assert.equal(list.length, n, `${what}: length`);
      const isArray: boolean = Array.isArray(list);
      assert.ok(isArray && typeof list === "object", `${what}: an array object`);
      elements.forEach((e, i) => assert.equal(list[i], e, `${what}: index ${i}`));
      assert.equal(list[n], undefined, `${what}: past the end`);
      assert.equal(Reflect.get(list, "0.5"), undefined, `${what}: a non-integer index`);
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
  console.log("C4: node lists of lengths 0, 1, 15, 16, 17 and 32 answer every transparent row as dense readonly arrays");
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

// C4 for the allocating members: each is declared as reviewed, and under Node
// two reads of a documented node's `jsDoc` give different arrays, while a
// stable member gives one value.
{
  const declarations = readFileSync(join(root, "dist", "ast", "ast.d.ts"), "utf8");
  for (const { owner, name, text } of allocatingMembers)
    assert.ok(declarations.includes(text), `${owner}.${name} is declared as reviewed: ${text}`);
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
  closeParser();
  console.log("C4: jsDoc allocates on each read; a stable member does not");
}
