// The compiler-API contract (COMPILER-API.md, "Binding the contract to the
// implementation") checked against the installed package, without a build.
//
// C1, enums: for every host enum the contract reads (`hostEnums` in
// tools/compiler-api.mts), each member of its `.enum.d.ts` is a plain integer
// literal equal to the value of the runtime object Node loads for
// `#enums/<file>` under the `default` condition, the runtime object's keys are
// exactly the members and their reverse mappings, and the entry points that
// export the enum export that object.
//
// C4, allocating members: each member the contract refuses as allocating is
// declared as reviewed, and under Node two reads of it give different values
// where a stable member gives one.
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { allocatingMembers, hostEnums, hostPackage, isHostFile } from "../tools/compiler-api.mts";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";

// The package the front end resolves, from tools/.
const root = dirname(createRequire(resolve(import.meta.dirname, "../tools/package.json"))
  .resolve(`${hostPackage.name}/package.json`));
const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
assert.ok(typeof manifest === "object" && manifest !== null, "the host package's manifest is an object");
assert.ok("name" in manifest && manifest.name === hostPackage.name && "version" in manifest &&
  manifest.version === hostPackage.version,
  `the installed host package is ${hostPackage.name} ${hostPackage.version}`);
assert.ok(isHostFile(join(root, "dist", "ast", "index.d.ts")), "the package's declarations are host files");

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
const exportsMap = new Map(Object.entries("exports" in manifest && typeof manifest.exports === "object" &&
  manifest.exports !== null ? manifest.exports : {}));
const entryPoint = async (path: string): Promise<Record<string, unknown>> => {
  const file = exportsMap.get(path);
  assert.ok(typeof file === "string", `the manifest exports ${path}`);
  return import(pathToFileURL(join(root, file)).href);
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
  const module: Record<string, unknown> = await import(pathToFileURL(join(root, target.replace("*", file))).href);
  const runtime = module[name];
  assert.ok(typeof runtime === "object" && runtime !== null, `${name}: the runtime module exports an object`);
  const values = new Map(Object.entries(runtime));
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

// C4 for the allocating members: each is declared as reviewed, and under Node
// two reads of a documented node's `jsDoc` give different arrays, while a
// stable member gives one value.
{
  const declarations = readFileSync(join(root, "dist", "ast", "ast.d.ts"), "utf8");
  for (const { owner, name, text } of allocatingMembers)
    assert.ok(declarations.includes(text), `${owner}.${name} is declared as reviewed: ${text}`);
  const file = join(mkdtempSync(join(tmpdir(), "tscert-jsdoc-")), "documented.ts");
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
