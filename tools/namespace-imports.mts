/* Namespace imports as named imports (SOURCE-ELABORATION.md, "Derived source
 * forms"; COMPILER-API.md, "Namespace imports and bitwise operators").
 *
 * `import * as ns from M`, where every occurrence of `ns` is a member read
 * `ns.x` or a qualified type name `ns.T`, is the named import of each `x` and
 * `T`: a module namespace object's members are the module's export bindings,
 * which a read finds as an import binding finds them. The elaboration writes
 * the file as that named import: the namespace import becomes blank text of
 * its length, each occurrence `ns.x` the identifier `ns$x` (one character
 * replaced), and one named import `import { x as ns$x, type T as ns$T } from
 * M;` is appended after the last statement. Every offset of the original text
 * outside the namespace import keeps its meaning, so a span of the elaborated
 * text is a span of the source.
 *
 * Refused: any other use of `ns` (`const m = ns`, `ns[k]`, `ns?.x`, `{ ns }`,
 * an export of it), a default import beside it, and an occurrence whose dot
 * is not the character after `ns`. A call `ns.f(…)` or a tagged template
 * `` ns.f`…` `` passes the namespace object as the receiver, where the named
 * import's call passes `undefined`; the two differ only for a function whose
 * contract states its receiver, so the declaration graph refuses such a call
 * where the callee's signatures state a `this` parameter (`receivers`).
 */
import type { Checker } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Identifier, ImportDeclaration, Node, SourceFile } from "typescript/unstable/ast";
import type { Span } from "./span.mts";

/** The elaborated text, and where the appended named imports start: an
 * offset at or past it locates the namespace import at `origin`.
 * `receivers` are the members called with the namespace as receiver, each
 * the span of its elaborated name (`ns$f`), which the declaration graph
 * checks in the project resolving the module. */
export type Elaboration = { text: string; appended: number; origin: number; receivers: NamespaceCall[] };
/** A callee `ns.f` as written, at the span of its elaborated name. */
export type NamespaceCall = { span: Span; written: string };

type Use = { member: string; value: boolean };

/** The namespace imports of `file` written as named imports, or null when it
 * has none. `fail` refuses a use outside the elaboration's syntax. */
export function elaborateNamespaceImports(file: SourceFile, checker: Checker,
    fail: (node: Node, message: string) => never): Elaboration | null {
  const imports = file.statements.filter((s): s is ImportDeclaration =>
    ts.isImportDeclaration(s) && !!s.importClause?.namedBindings && ts.isNamespaceImport(s.importClause.namedBindings));
  const [first] = imports;
  if (!first) return null;
  const text = file.getFullText();
  // One entry per UTF-16 code unit, as offsets count.
  const chars = text.split("");
  const identifiers = new Set<string>();
  const occurrences = new Map<string, Identifier[]>();
  const collect = (node: Node): void => {
    if (ts.isIdentifier(node)) {
      identifiers.add(node.text);
      const list = occurrences.get(node.text);
      if (list) list.push(node);
      else occurrences.set(node.text, [node]);
    }
    node.forEachChild(collect);
  };
  collect(file);
  const appended: string[] = [];
  const receivers: NamespaceCall[] = [];
  for (const declaration of imports) {
    const clause = declaration.importClause;
    const bindings = clause?.namedBindings;
    if (!clause || !bindings || !ts.isNamespaceImport(bindings)) continue;
    if (clause.name) fail(declaration, "a default import beside a namespace import is outside the source fragment");
    if (declaration.attributes) fail(declaration, "import attributes are outside the source fragment");
    if (!ts.isStringLiteral(declaration.moduleSpecifier))
      fail(declaration, "a namespace import names its module by a string literal");
    const typeOnly = "isTypeOnly" in clause && clause.isTypeOnly === true;
    const namespace = bindings.name;
    const symbol = checker.getSymbolAtLocation(namespace);
    if (!symbol) fail(namespace, `TypeScript binds no namespace to ${namespace.text}`);
    const candidates = (occurrences.get(namespace.text) ?? []).filter(id => id !== namespace);
    const symbols = checker.getSymbolAtLocation(candidates);
    const uses = new Map<string, Use>();
    candidates.forEach((id, i) => {
      if (symbols[i]?.id !== symbol.id) return;
      const parent = id.parent;
      const member = parent && ts.isPropertyAccessExpression(parent) && parent.expression === id &&
          !parent.questionDotToken && ts.isIdentifier(parent.name) ? { node: parent, name: parent.name, value: true }
        : parent && ts.isQualifiedName(parent) && parent.left === id ? { node: parent, name: parent.right, value: false }
        : null;
      if (!member)
        fail(id, `the namespace import ${namespace.text} is used only through member reads and qualified type names`);
      const dot = id.end;
      if (text[dot] !== "." || member.name.getStart(file) !== dot + 1)
        fail(id, `a member read of the namespace import ${namespace.text} is written \`${namespace.text}.name\``);
      if (member.value && receiverCall(member.node))
        receivers.push({ span: [id.getStart(file), member.name.end], written: `${namespace.text}.${member.name.text}` });
      chars[dot] = "$";
      const known = uses.get(member.name.text);
      uses.set(member.name.text, { member: member.name.text, value: member.value || (known?.value ?? false) });
    });
    const specifiers = [...uses.values()].map(use => {
      const local = `${namespace.text}$${use.member}`;
      if (identifiers.has(local))
        fail(namespace, `the namespace import ${namespace.text} needs the name ${local}, which the file binds`);
      return `${typeOnly || !use.value ? "type " : ""}${use.member} as ${local}`;
    });
    for (let i = declaration.getStart(file); i < declaration.end; i++)
      if (chars[i] !== "\n" && chars[i] !== "\r") chars[i] = " ";
    if (specifiers.length)
      appended.push(`import { ${specifiers.join(", ")} } from ${JSON.stringify(declaration.moduleSpecifier.text)};`);
  }
  const body = chars.join("");
  const separator = body.endsWith("\n") ? "" : "\n";
  return { text: `${body}${separator}${appended.join("\n")}\n`, appended: body.length + separator.length,
    origin: first.getStart(file), receivers };
}

/** Whether a member read is the callee of a call or a tagged template, which
 * passes its object as the receiver, through parentheses too. */
function receiverCall(access: Node): boolean {
  let callee: Node = access;
  while (callee.parent && ts.isParenthesizedExpression(callee.parent)) callee = callee.parent;
  const parent = callee.parent;
  return !!parent && ((ts.isCallExpression(parent) && parent.expression === callee) ||
    (ts.isTaggedTemplateExpression(parent) && parent.tag === callee));
}
