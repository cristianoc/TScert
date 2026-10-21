// The family interpreter (`tools/host-families.mts`, HOST-FAMILIES.md, "The
// family contract") on a description of declarations no audited package has:
// a generic shape whose other members depend on its tag parameter, which the
// pipeline cannot reach through the compiler API. Its applications at
// different tags stay separate arms, where a generic whose tag alone varies
// merges them into one arm at their tag set; a residual keeps the members
// every replaced shape has, optional where one is; a refinement is no shape;
// and a name two unrelated bases state is refused. A tag enum object with a
// reverse key missing, inherited, an accessor, a number, naming a member of
// another value, or beside an extra key, is no emitted enum object.
import assert from "node:assert/strict";
import { writeFileSync } from "node:fs";
import { join } from "node:path";
import { syntax as ts } from "../tools/syntax.mts";
import { familyTable, type FamilyDescription, type FamilyGraph } from "../tools/host-families.mts";
import { enumObjectMatches } from "../tools/family-activation.mts";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { runDirectory } from "../pipeline/run-directory.mts";

const source = `
declare enum K { A = 0, B = 1, C = 2, D = 3, E = 4, F = 5 }
export interface Node { readonly kind: K; readonly parent: Node; }
export interface Base extends Node { readonly note?: string; }
export interface Tok<T extends K.A | K.B = K.A | K.B> extends Base { readonly kind: T; }
export interface Tagged<T extends K.C | K.D = K.C | K.D> extends Base { readonly kind: T; readonly same: T; }
export interface Lit extends Base { readonly kind: K.E; readonly x: number; }
export interface Sub extends Lit { readonly x: 1; }
`;
const file = join(runDirectory("tscert-families-"), "family.d.ts");
writeFileSync(file, source);
const tree = openText(file, source);
const interfaces = tree.statements.filter(ts.isInterfaceDeclaration);
const enumeration = tree.statements.find(ts.isEnumDeclaration);
assert.ok(enumeration, "the tag enum");
const constants = enumeration.members.map((m, i) => ({ name: m.name.getText(tree), value: i }));
const byName = (name: string): ts.InterfaceDeclaration | undefined => interfaces.find(d => d.name.text === name);
const literals = (type: ts.TypeNode): number[] | null => {
  if (ts.isUnionTypeNode(type)) {
    const parts = type.types.map(literals);
    return parts.every((p): p is number[] => p !== null) ? parts.flat().sort((a, b) => a - b) : null;
  }
  if (ts.isTypeReferenceNode(type) && ts.isQualifiedName(type.typeName)) {
    const member = type.typeName.right.text;
    const found = constants.find(c => c.name === member);
    return found ? [found.value] : null;
  }
  return null;
};
const description: FamilyDescription = {
  package: { name: "fixture", version: "0.0.0" },
  installation: { from: "", digest: "" },
  marker: "Fixture",
  root: { name: "Node", form: "inheritance", text: "export interface Node { readonly kind: K; readonly parent: Node; }" },
  tag: { field: "kind", primitive: "number", constants: { enum: "K" } },
  table: [{ rule: "literal" }, { rule: "generic", declarations: ["Tok", "Tagged"] }, { rule: "base", declaration: "Base" }],
  corrections: [],
  allocating: [],
  stable: { excluded: [] },
  guards: { entryPoint: "", conditions: [], entryModule: "", closure: { files: {}, edges: [] }, helpers: {}, guards: [], excluded: [] },
};
const graph = (declarations: readonly ts.InterfaceDeclaration[]): FamilyGraph => ({
  interfaces: declarations,
  bases: d => (d.heritageClauses ?? []).flatMap(c => c.types.map(t => {
    const found = byName(t.expression.getText(tree));
    assert.ok(found, `the base ${t.expression.getText(tree)}`);
    return found;
  })),
  literals,
  values: constants.map(c => c.value),
  constantName: v => constants.find(c => c.value === v)?.name ?? String(v),
  tagParameter: d => {
    const own = d.members.find(m => ts.isPropertySignatureDeclaration(m) && m.name.getText(tree) === "kind");
    const type = own && ts.isPropertySignatureDeclaration(own) ? own.type : undefined;
    const name = type && ts.isTypeReferenceNode(type) && ts.isIdentifier(type.typeName) ? type.typeName.text : null;
    return name !== null && (d.typeParameters ?? []).some(p => p.name.text === name) ? name : null;
  },
  questioned: m => ts.isPropertySignatureDeclaration(m) && m.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
  name: m => ts.isPropertySignatureDeclaration(m) && ts.isIdentifier(m.name) ? m.name.text : null,
  text: m => m.getText(tree).trim(),
  mentions: (m, parameter) => {
    const visit = (n: ts.Node): boolean => (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName) &&
      n.typeName.text === parameter) || (n.forEachChild(visit) ?? false);
    return visit(m);
  },
  fail: message => { throw Error(message); },
});
const table = familyTable(description, graph(interfaces));
const node = byName("Node");
const lit = byName("Lit");
const sub = byName("Sub");
assert.ok(node && lit && sub, "the fixture's declarations");

// The table: a literal declaration, the generics at their bounds, the base.
assert.deepEqual([...table.shapes].map(([t, s]) => `${t}:${s.rule}`), ["0:generic", "1:generic", "2:generic", "3:generic", "4:literal", "5:base"]);
const four = table.shapes.get(4);
assert.ok(four?.rule === "literal" && four.declaration === lit, "the literal declaration, not its refinement, is the shape");
assert.deepEqual(table.tagOf(sub), { k: "literal", values: [4] });
assert.deepEqual(table.membersOf(node), [0, 1, 2, 3, 4, 5]);

// Every tag selected: `Tok` merged at its tag set, `Tagged` one arm per tag,
// since its `same` member is its tag parameter.
const every = table.arms(node, new Set([0, 1, 2, 3, 4, 5]));
assert.deepEqual(every.map(a => a.k === "declaration" ? a.declaration.name.text
  : a.k === "generic" ? `${a.declarations.map(g => g.name.text).join("&")}<${a.values.join("|")}>` : a.name.split(" ")[0]),
  ["Tok<0|1>", "Tagged<2>", "Tagged<3>", "Lit", "Base"], "the arms in tag order");

// No tag selected: one residual, its members those every shape has.
const [residual, ...others] = table.arms(node, new Set());
assert.ok(residual?.k === "synthetic" && !others.length, "one residual arm");
assert.deepEqual(residual.values, [0, 1, 2, 3, 4, 5]);
assert.deepEqual(residual.fields.map(f => `${f.name}${f.optional ? "?" : ""}`), ["note?", "parent"]);

// The stable-member rule (HOST-FAMILIES.md, "Stable keys"): every property
// member is stable but the exclusions, each a member its owner declares as
// reviewed; an exclusion naming no member, or at another text, is refused.
const litX = table.flatten(lit).find(f => f.name === "x");
assert.ok(litX && table.stable(litX), "a member no exclusion names is stable");
const excluding = familyTable({ ...description,
  stable: { excluded: [{ owner: "Lit", member: "x", text: "readonly x: number;" }] } }, graph(interfaces));
assert.ok(!excluding.stable(litX), "an excluded member is not stable");
assert.throws(() => familyTable({ ...description,
  stable: { excluded: [{ owner: "Lit", member: "y", text: "readonly y: number;" }] } }, graph(interfaces)),
  /the stable-member rule excludes Lit\.y, which is not declared as reviewed/);
assert.throws(() => familyTable({ ...description,
  stable: { excluded: [{ owner: "Lit", member: "x", text: "readonly x: string;" }] } }, graph(interfaces)),
  /the stable-member rule excludes Lit\.x, which is not declared as reviewed/);
// An allocating member (HOST-FAMILIES.md, "The family contract") is no
// member of any shape; one not declared as reviewed is refused.
assert.ok(table.flatten(lit).some(f => f.name === "note"), "an unlisted member is a member");
const allocating = familyTable({ ...description,
  allocating: [{ owner: "Base", member: "note", text: "readonly note?: string;" }] }, graph(interfaces));
assert.ok(!allocating.flatten(lit).some(f => f.name === "note"), "an allocating member is no member");
assert.throws(() => familyTable({ ...description,
  allocating: [{ owner: "Base", member: "note", text: "readonly note: string;" }] }, graph(interfaces)),
  /the allocating member Base\.note is not declared as reviewed/);
closeParser();

// A generic shape with a parameter beside its tag parameter, which the
// reading would apply at its tag as its first argument.
{
  const text = `
declare enum K { A = 0, B = 1 }
export interface Node { readonly kind: K; }
export interface Pair<U = string, T extends K.A | K.B = K.A | K.B> extends Node { readonly kind: T; readonly other: U; }
`;
  const other = join(runDirectory("tscert-families-"), "pair.d.ts");
  writeFileSync(other, text);
  const paired = openText(other, text);
  const declarations = paired.statements.filter(ts.isInterfaceDeclaration);
  const g = { ...graph(declarations), values: [0, 1],
    bases: (d: ts.InterfaceDeclaration): ts.InterfaceDeclaration[] => (d.heritageClauses ?? []).flatMap(c => c.types.map(t => {
      const found = declarations.find(x => x.name.text === t.expression.getText(paired));
      assert.ok(found);
      return found;
    })),
    tagParameter: (d: ts.InterfaceDeclaration): string | null => d.name.text === "Pair" ? "T" : null,
    text: (m: ts.Node): string => m.getText(paired).trim() };
  assert.throws(() => familyTable({ ...description, table: [{ rule: "generic", declarations: ["Pair"] }] }, g),
    /Pair has parameters beside its tag parameter/);
  closeParser();
}

// A name two bases state through declarations neither extending the other.
{
  const text = `
declare enum K { A = 0 }
export interface Node { readonly kind: K; }
export interface Left extends Node { readonly side: number; }
export interface Right extends Node { readonly side: string; }
export interface Both extends Left, Right { readonly kind: K.A; }
`;
  const other = join(runDirectory("tscert-families-"), "conflict.d.ts");
  writeFileSync(other, text);
  const conflicted = openText(other, text);
  const declarations = conflicted.statements.filter(ts.isInterfaceDeclaration);
  const g = { ...graph(declarations), values: [0],
    bases: (d: ts.InterfaceDeclaration): ts.InterfaceDeclaration[] => (d.heritageClauses ?? []).flatMap(c => c.types.map(t => {
      const found = declarations.find(x => x.name.text === t.expression.getText(conflicted));
      assert.ok(found);
      return found;
    })),
    text: (m: ts.Node): string => m.getText(conflicted).trim() };
  assert.throws(() => familyTable({ ...description, table: [{ rule: "literal" }] }, g),
    /Both inherits side from Left and Right, neither extending the other/);
  closeParser();
}
console.log("family interpreter: a tag-only generic merged at its tag set, a tag-dependent one kept per tag; " +
  "a residual's common members; a refinement no shape; a stable-member exclusion as reviewed, and one naming no member or another text refused; " +
  "an allocating member omitted, one at another text refused; " +
  "a generic with a parameter beside its tag, and an unrelated inherited name, refused");

// A tag enum's runtime object (`enumObjectMatches`, HOST-FAMILIES.md,
// "Activation"): the emitted object matches its declaration; one whose
// reverse key is missing, inherited, an accessor, a number, or the name of a
// member of another value, or with a key of its own beside them, does not.
{
  const declared = [{ name: "A", value: 0 }, { name: "B", value: 1 }, { name: "C", value: 1 }];
  const emitted = (): Record<string, unknown> => ({ A: 0, B: 1, C: 1, 0: "A", 1: "C" });
  assert.ok(enumObjectMatches(emitted(), declared), "the emitted object");
  assert.ok(enumObjectMatches({ ...emitted(), 1: "B" }, declared), "a reverse key naming another member of its value");
  const missing = emitted();
  delete missing[1];
  const inherited = { A: 0, B: 1, C: 1, 0: "A" };
  assert.ok(Reflect.setPrototypeOf(inherited, { 1: "C" }));
  const accessor = { A: 0, B: 1, C: 1, 0: "A", get 1(): string { return "C"; } };
  for (const [what, object] of [["missing", missing], ["inherited", inherited], ["an accessor", accessor],
    ["a number", { ...emitted(), 1: 1 }], ["another value's member", { ...emitted(), 1: "A" }],
    ["an extra key", { ...emitted(), 2: "A" }]] as const)
    assert.ok(!enumObjectMatches(object, declared), `a reverse key ${what}`);
}
console.log("tag enum objects: the emitted object matches; a reverse key missing, inherited, an accessor, a number, " +
  "naming a member of another value, or an extra key, refused");
