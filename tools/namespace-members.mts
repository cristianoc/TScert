/* The members a file reads through its namespace imports (SOURCE-ELABORATION.md,
 * "Derived source forms"; COMPILER-API.md, "Namespace imports and bitwise
 * operators").
 *
 * `import * as ns from M`, where every mention TypeScript binds to `ns` is a
 * member read `ns.x` or a qualified type name `ns.T`, imports each member it
 * names: a module namespace object's members are the module's export
 * bindings, which a member read finds as an import binding finds them. Each
 * member is one binding of the file, named `ns.x`, which no identifier
 * spells; every occurrence keeps its own span and spelling, the parser
 * lowers a read of it as a read of that binding, and the declaration graph
 * resolves it, through the checker, to the export the member names.
 *
 * Any other mention of `ns` (`const m = ns`, `ns[k]`, `ns?.x`, `{ ns }`, an
 * export of it) and a member written (`ns.x = e`, `ns.x++`, `delete ns.x`,
 * a destructuring target) are refused at the mention.
 *
 * A default import of a module that exports a function merged with a
 * namespace, whose members the overlay of library modules reviews
 * (`import assert from "node:assert/strict"`), is read the same way: each
 * member read `assert.m` is the binding `assert.m`, of the export
 * `default.m`, and a call `assert(…)` stays a call of the import's own
 * binding. Any other mention is refused. */
import { moduleEntries } from "./library-modules.mts";
import type { Checker } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Expression, Identifier, ImportDeclaration, Node, SourceFile } from "typescript/unstable/ast";
import type { Span } from "./span.mts";

/** One occurrence of a member: the member read or qualified name `node`,
 * whose name is `name`, and whether it is a value read and whether it is a
 * call's callee, which passes the namespace object as the receiver. */
export type MemberUse = { node: ts.PropertyAccessExpression | ts.QualifiedName; name: Identifier; value: boolean;
  callee: boolean };
/** A namespace import's members: the binding each is, `ns.x`, the export it
 * names, the import's specifier, and its occurrences, in source order. */
export type NamespaceMember = { local: string; imported: string; specifier: string; uses: MemberUse[] };

/** The binding a namespace member is: a name no identifier spells. */
export const memberLocal = (namespace: string, member: string): string => `${namespace}.${member}`;

/** The members `file` reads through its namespace imports, by binding name.
 * `fail` refuses a mention outside member reads and qualified names. */
export function namespaceMembers(file: SourceFile, checker: Checker,
    fail: (node: Node, message: string) => never): Map<string, NamespaceMember> {
  const members = new Map<string, NamespaceMember>();
  const imports = file.statements.filter((s): s is ImportDeclaration =>
    ts.isImportDeclaration(s) && !!s.importClause?.namedBindings && ts.isNamespaceImport(s.importClause.namedBindings));
  // Default imports of a function merged with a namespace the overlay reviews.
  const functions = file.statements.filter((s): s is ImportDeclaration =>
    ts.isImportDeclaration(s) && !!s.importClause?.name &&
    (!s.importClause.namedBindings || ts.isNamedImports(s.importClause.namedBindings)) &&
    ts.isStringLiteral(s.moduleSpecifier) &&
    moduleEntries(s.moduleSpecifier.text, "default").some(e => e.member !== undefined));
  if (!imports.length && !functions.length) return members;
  const occurrences = new Map<string, Identifier[]>();
  const collect = (node: Node): void => {
    if (ts.isIdentifier(node)) {
      const list = occurrences.get(node.text);
      if (list) list.push(node);
      else occurrences.set(node.text, [node]);
    }
    node.forEachChild(collect);
  };
  collect(file);
  for (const declaration of functions) {
    const name = declaration.importClause?.name;
    if (!name || !ts.isStringLiteral(declaration.moduleSpecifier)) continue;
    const specifier = declaration.moduleSpecifier.text;
    const symbol = checker.getSymbolAtLocation(name);
    if (!symbol) fail(name, `TypeScript binds no default import to ${name.text}`);
    const candidates = (occurrences.get(name.text) ?? []).filter(id => id !== name);
    const symbols = checker.getSymbolAtLocation(candidates);
    candidates.forEach((id, i) => {
      if (symbols[i]?.id !== symbol.id) return;
      const parent = id.parent;
      if (parent && ts.isCallExpression(parent) && parent.expression === id) return;
      if (!parent || !ts.isPropertyAccessExpression(parent) || parent.expression !== id || parent.questionDotToken ||
          !ts.isIdentifier(parent.name) || !callee(parent))
        fail(id, `the default import ${name.text} is only called, or its members called`);
      const use: MemberUse = { node: parent, name: parent.name, value: true, callee: true };
      const local = memberLocal(name.text, parent.name.text);
      const known = members.get(local);
      if (known) known.uses.push(use);
      else members.set(local, { local, imported: `default.${parent.name.text}`, specifier, uses: [use] });
    });
  }
  for (const declaration of imports) {
    const clause = declaration.importClause;
    const bindings = clause?.namedBindings;
    if (!clause || !bindings || !ts.isNamespaceImport(bindings)) continue;
    if (clause.name) fail(declaration, "a default import beside a namespace import is outside the source fragment");
    if (declaration.attributes) fail(declaration, "import attributes are outside the source fragment");
    if (!ts.isStringLiteral(declaration.moduleSpecifier))
      fail(declaration, "a namespace import names its module by a string literal");
    const specifier = declaration.moduleSpecifier.text;
    const typeOnly = "isTypeOnly" in clause && clause.isTypeOnly === true;
    const namespace = bindings.name;
    const symbol = checker.getSymbolAtLocation(namespace);
    if (!symbol) fail(namespace, `TypeScript binds no namespace to ${namespace.text}`);
    const candidates = (occurrences.get(namespace.text) ?? []).filter(id => id !== namespace);
    const symbols = checker.getSymbolAtLocation(candidates);
    candidates.forEach((id, i) => {
      if (symbols[i]?.id !== symbol.id) return;
      const parent = id.parent;
      const use: MemberUse | null =
        parent && ts.isPropertyAccessExpression(parent) && parent.expression === id && !parent.questionDotToken &&
            ts.isIdentifier(parent.name)
          ? { node: parent, name: parent.name, value: true, callee: callee(parent) }
          : parent && ts.isQualifiedName(parent) && parent.left === id
            ? { node: parent, name: parent.right, value: false, callee: false }
            : null;
      if (!use)
        fail(id, `the namespace import ${namespace.text} is used only through member reads and qualified type names`);
      if (use.value && typeOnly) fail(use.node, `the type-only namespace import ${namespace.text} is read as a value`);
      if (use.value && ts.isPropertyAccessExpression(use.node) && written(use.node))
        fail(use.node, `a member of the namespace import ${namespace.text} is an import binding, which no code writes`);
      const local = memberLocal(namespace.text, use.name.text);
      const known = members.get(local);
      if (known) known.uses.push(use);
      else members.set(local, { local, imported: use.name.text, specifier,
        uses: [use] });
    });
  }
  return members;
}

/** The members of `members` keyed by the span of each occurrence. */
export function memberUses(members: ReadonlyMap<string, NamespaceMember>, file: SourceFile):
    Map<string, { member: NamespaceMember; use: MemberUse }> {
  const uses = new Map<string, { member: NamespaceMember; use: MemberUse }>();
  for (const member of members.values())
    for (const use of member.uses) uses.set(spanKey([use.node.getStart(file), use.node.end]), { member, use });
  return uses;
}

const spanKey = (span: Span): string => `${span[0]}:${span[1]}`;

/** Whether a member read is the callee of a call or a tagged template,
 * through parentheses too: JavaScript passes its object as the receiver. */
function callee(access: Node): boolean {
  let at: Node = access;
  while (at.parent && ts.isParenthesizedExpression(at.parent)) at = at.parent;
  const parent = at.parent;
  return !!parent && ((ts.isCallExpression(parent) && parent.expression === at) ||
    (ts.isTaggedTemplateExpression(parent) && parent.tag === at));
}

/** Whether a member read is written: an assignment's or an update's target,
 * `delete`'s operand, a destructuring assignment's target, or a `for…in` or
 * `for…of` head's. */
function written(access: Expression): boolean {
  let at: Node = access;
  for (;;) {
    const parent = at.parent;
    if (!parent) return false;
    if (ts.isParenthesizedExpression(parent) || ts.isArrayLiteralExpression(parent) || ts.isSpreadElement(parent) ||
        ts.isObjectLiteralExpression(parent) || ts.isSpreadAssignment(parent) ||
        (ts.isPropertyAssignment(parent) && parent.initializer === at)) {
      at = parent;
      continue;
    }
    if (ts.isBinaryExpression(parent))
      return parent.left === at && parent.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        parent.operatorToken.kind <= ts.SyntaxKind.LastAssignment;
    if (ts.isPrefixUnaryExpression(parent) || ts.isPostfixUnaryExpression(parent))
      return parent.operator === ts.SyntaxKind.PlusPlusToken || parent.operator === ts.SyntaxKind.MinusMinusToken;
    if (ts.isDeleteExpression(parent)) return true;
    if (ts.isForInStatement(parent) || ts.isForOfStatement(parent)) return parent.initializer === at;
    return false;
  }
}
