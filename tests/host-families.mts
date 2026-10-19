// The family interpreter (`tools/host-families.mts`, HOST-FAMILIES.md, "The
// family contract") on a description of declarations no audited package has:
// a generic shape whose other members depend on its tag parameter, which the
// pipeline cannot reach through the compiler API. Its applications at
// different tags stay separate arms, where a generic whose tag alone varies
// merges them into one arm at their tag set; a residual keeps the members
// every replaced shape has, optional where one is; a refinement is no shape;
// and a name two unrelated bases state is refused.
import assert from "node:assert/strict";
import { writeFileSync } from "node:fs";
import { join } from "node:path";
import { syntax as ts } from "../tools/syntax.mts";
import { familyTable, type FamilyDescription, type FamilyGraph } from "../tools/host-families.mts";
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
  package: "fixture",
  marker: "Fixture",
  root: { name: "Node", form: "inheritance", text: "export interface Node { readonly kind: K; readonly parent: Node; }" },
  tag: { field: "kind", primitive: "number", constants: { enum: "K" } },
  table: [{ rule: "literal" }, { rule: "generic", declarations: ["Tok", "Tagged"] }, { rule: "base", declaration: "Base" }],
  corrections: [],
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
  omitted: () => false,
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
  ["Lit", "Tok<0|1>", "Tagged<2>", "Tagged<3>", "Base"]);

// No tag selected: one residual, its members those every shape has.
const [residual, ...others] = table.arms(node, new Set());
assert.ok(residual?.k === "synthetic" && !others.length, "one residual arm");
assert.deepEqual(residual.values, [0, 1, 2, 3, 4, 5]);
assert.deepEqual(residual.fields.map(f => `${f.name}${f.optional ? "?" : ""}`), ["note?", "parent"]);
closeParser();

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
  "a residual's common members; a refinement no shape; an unrelated inherited name refused");
