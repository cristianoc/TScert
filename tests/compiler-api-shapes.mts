// C3, the presence of the properties a shape states required, against run
// time (COMPILER-API.md, "Binding the contract to the implementation"):
// every node of a corpus, the JSDoc nodes each holds included, holds every
// property its kind's flattened shape states required and not admitting
// `undefined`, inherited and generic components included, unless a
// correction of the compiler API's family covers it. Methods, member types,
// children's kinds and stability are not checked here: this is presence
// regression evidence over the corpus, not a completeness proof. The shapes are the
// family table's (`tools/host-families.mts`) over the installed package's
// declarations, resolved by name; the corpus is the repository's own sources
// and fixtures and `tests/node-shapes-corpus/`. What the corpus never reaches
// is reported: the kinds no node has, and the members of reached kinds no
// node holds, the brands declared `any` aside. About 20 s: `make
// compiler-api-shapes`, outside the fast checks.
//   node tests/compiler-api-shapes.mts
import assert from "node:assert/strict";
import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { compilerApiFamily, hostPackage } from "../tools/compiler-api.mts";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { familyTable, type FamilyGraph, type FlatMember, type TagValue } from "../tools/host-families.mts";
import { syntax as ts } from "../tools/syntax.mts";
import { runDirectory } from "../pipeline/run-directory.mts";

const repository = resolve(import.meta.dirname, "..");
const root = dirname(createRequire(resolve(repository, "tools/package.json")).resolve(`${hostPackage.name}/package.json`));

// The package's node declarations, by name.
const scratch = runDirectory("tscert-shapes-");
const declarationFiles = ["ast.d.ts", "ast.generated.d.ts"].map((name) => {
  const copy = join(scratch, name);
  const text = readFileSync(join(root, "dist", "ast", name), "utf8");
  writeFileSync(copy, text);
  return openText(copy, text);
});
const interfaces = new Map<string, ts.InterfaceDeclaration>();
const aliases = new Map<string, ts.TypeAliasDeclaration>();
for (const file of declarationFiles)
  for (const statement of file.statements) {
    if (ts.isInterfaceDeclaration(statement)) interfaces.set(statement.name.text, statement);
    if (ts.isTypeAliasDeclaration(statement)) aliases.set(statement.name.text, statement);
  }
const textOf = (node: ts.Node): string => node.getText(node.getSourceFile()).trim();
const basesOf = (d: ts.InterfaceDeclaration): ts.InterfaceDeclaration[] =>
  (d.heritageClauses ?? []).flatMap((c) => c.types.flatMap((t) => {
    const found = interfaces.get(textOf(t.expression));
    return found ? [found] : [];
  }));
const reaches = (d: ts.InterfaceDeclaration, seen: Set<ts.InterfaceDeclaration> = new Set()): boolean =>
  d.name.text === compilerApiFamily.root.name || (!seen.has(d) && (seen.add(d), basesOf(d).some((b) => reaches(b, seen))));
const kinds = new Map<string, number>(Object.entries(ts.SyntaxKind).flatMap(([name, value]): [string, number][] =>
  typeof value === "number" ? [[name, value]] : []));
const literals = (type: ts.TypeNode, seen: Set<string> = new Set()): number[] | null => {
  if (ts.isParenthesizedTypeNode(type)) return literals(type.type, seen);
  if (ts.isUnionTypeNode(type)) {
    const parts = type.types.map((t) => literals(t, seen));
    return parts.every((p): p is number[] => p !== null) ? [...new Set(parts.flat())].sort((a, b) => a - b) : null;
  }
  if (!ts.isTypeReferenceNode(type)) return null;
  if (ts.isQualifiedName(type.typeName)) {
    const value = kinds.get(type.typeName.right.text);
    return value === undefined ? null : [value];
  }
  const name = type.typeName.text;
  const alias = aliases.get(name);
  if (!alias || seen.has(name)) return null;
  seen.add(name);
  return literals(alias.type, seen);
};
const memberName = (m: ts.TypeElement): string | null =>
  (ts.isPropertySignatureDeclaration(m) || ts.isMethodSignatureDeclaration(m)) && ts.isIdentifier(m.name) ? m.name.text : null;
const graph: FamilyGraph = {
  interfaces: [...interfaces.values()].filter((d) => reaches(d)),
  bases: basesOf,
  literals,
  values: [...new Set(kinds.values())].sort((a, b) => a - b),
  constantName: (value) => [...kinds].find(([, v]) => v === value)?.[0] ?? String(value),
  tagParameter: (d) => {
    const own = d.members.find((m) => memberName(m) === compilerApiFamily.tag.field);
    const type = own && ts.isPropertySignatureDeclaration(own) ? own.type : undefined;
    const name = type && ts.isTypeReferenceNode(type) && ts.isIdentifier(type.typeName) ? type.typeName.text : null;
    return name !== null && (d.typeParameters ?? []).some((p) => p.name.text === name) ? name : null;
  },
  questioned: (m) => (ts.isPropertySignatureDeclaration(m) || ts.isMethodSignatureDeclaration(m)) &&
    m.postfixToken?.kind === ts.SyntaxKind.QuestionToken,
  name: memberName,
  text: textOf,
  mentions: (m, parameter) => {
    const visit = (n: ts.Node): boolean => (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName) &&
      n.typeName.text === parameter) || (n.forEachChild(visit) ?? false);
    return visit(m);
  },
  fail: (message) => { throw Error(message); },
};
const table = familyTable(compilerApiFamily, graph);

// A property a node of kind `k` must hold: stated, required at `k` and
// uncorrected, its type admitting neither `undefined` nor anything (`any`).
const admitsUndefined = (type: ts.TypeNode | undefined): boolean => !type ||
  type.kind === ts.SyntaxKind.AnyKeyword || type.kind === ts.SyntaxKind.UndefinedKeyword ||
  (ts.isUnionTypeNode(type) && type.types.some(admitsUndefined)) ||
  (ts.isParenthesizedTypeNode(type) && admitsUndefined(type.type));
const requiredAt = new Map<TagValue, FlatMember[]>();
const required = (k: TagValue): FlatMember[] => {
  const known = requiredAt.get(k);
  if (known) return known;
  const source = table.shapes.get(k);
  const flat = !source ? [] : source.rule === "generic" ? source.declarations.flatMap(table.flatten) : table.flatten(source.declaration);
  const result = flat.filter((f) => f.name !== compilerApiFamily.tag.field && !table.optional(f, [k]) &&
    f.members.every((m) => ts.isPropertySignatureDeclaration(m) && !admitsUndefined(m.type)));
  requiredAt.set(k, result);
  return result;
};

// The corpus: the repository's own sources and fixtures, and the synthetic
// files exercising the kinds they leave out.
const sources = (dir: string, pattern: RegExp): string[] =>
  readdirSync(join(repository, dir)).filter((f) => pattern.test(f)).map((f) => join(repository, dir, f));
const corpus = [
  ...sources("tools", /\.mts$/), ...sources("pipeline", /\.mts$/), ...sources("tests", /\.mts$/), ...sources("dev", /\.mts$/),
  ...sources("pipeline/examples", /\.ts$/),
  ...sources("tests/node-shapes-corpus", /\.(ts|tsx|js)$/),
];
const isNode = (value: unknown): value is ts.Node =>
  typeof value === "object" && value !== null && "kind" in value && typeof value.kind === "number";
const seenKinds = new Set<TagValue>();
const held = new Set<string>();
const absent = new Map<string, number>();
let nodes: number = 0;
for (const path of corpus) {
  const tree = openText(path, readFileSync(path, "utf8"));
  const visit = (node: ts.Node): undefined => {
    nodes++;
    seenKinds.add(node.kind);
    const source = table.shapes.get(node.kind);
    const flat = !source ? [] : source.rule === "generic" ? source.declarations.flatMap(table.flatten) : table.flatten(source.declaration);
    for (const f of flat) if (Reflect.get(node, f.name) !== undefined) held.add(`${node.kind}.${f.name}`);
    for (const f of required(node.kind))
      if (Reflect.get(node, f.name) === undefined) {
        const key = `${graph.constantName(node.kind)}: ${f.owner.name.text}.${f.name}`;
        absent.set(key, (absent.get(key) ?? 0) + 1);
      }
    // JSDoc is no child: each documented node holds its comments apart.
    const docs: unknown = Reflect.get(node, "jsDoc");
    if (Array.isArray(docs)) for (const doc of docs.filter(isNode)) visit(doc);
    return node.forEachChild(visit);
  };
  visit(tree);
}
closeParser();

// An unreached kind whose shape states no checked property beyond the
// root's and `NodeBase`'s, which every reached node is checked for (a token,
// a keyword, trivia), leaves no property of its own unchecked; the others
// are listed apart.
const common = new Set([compilerApiFamily.root.name, "NodeBase", "ReadonlyTextRange"]);
const ownRequired = (k: TagValue): FlatMember[] => required(k).filter((f) => !common.has(f.owner.name.text));
const unreachedKinds = [...table.shapes.keys()].filter((k) => !seenKinds.has(k));
const unreached = unreachedKinds.filter((k) => !ownRequired(k).length).map(graph.constantName);
const uncovered = unreachedKinds.filter((k) => ownRequired(k).length).map((k) =>
  `${graph.constantName(k)} (${ownRequired(k).map((f) => f.name).join(", ")})`);
const unheld = [...seenKinds].flatMap((k) => {
  const source = table.shapes.get(k);
  const flat = !source ? [] : source.rule === "generic" ? source.declarations.flatMap(table.flatten) : table.flatten(source.declaration);
  return flat.filter((f) => f.name !== compilerApiFamily.tag.field && !held.has(`${k}.${f.name}`) &&
    f.members.every((m) => !ts.isPropertySignatureDeclaration(m) || m.type?.kind !== ts.SyntaxKind.AnyKeyword))
    .map((f) => `${graph.constantName(k)}.${f.name}`);
});
console.log(`C3: ${nodes} nodes of ${corpus.length} files, ${seenKinds.size} of ${table.shapes.size} kinds reached`);
console.log(`  kinds no node has, stating no checked property of its own (${unreached.length}): ${unreached.join(" ")}`);
console.log(`  kinds no node has, stating checked properties of its own (${uncovered.length}): ${uncovered.join(" ")}`);
console.log(`  members of reached kinds no node holds (${unheld.length}): ${unheld.join(" ")}`);
assert.deepEqual([...absent].map(([key, count]) => `${key} (${count} nodes)`), [],
  "a member a shape states required is absent at run time, and no correction covers it");
console.log("C3: every checked required property of a reached kind's shape is held by every node of that kind, or corrected (presence regression evidence)");
