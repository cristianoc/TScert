/** The executable ES module closure of an audited guard entry point.
 * Reading and parsing sources and resolving URLs performs no module load.
 * Digests bind all executable code, including indirect loading through
 * computed properties, to the reviewed sources. */
import { createHash } from "node:crypto";
import * as ts from "typescript/unstable/ast";

export type ModuleEdge = readonly [from: string, local: string, target: string, exported: string,
  attributes: readonly (readonly [string, string])[], kind: "import" | "export"];
export type GuardClosure = {
  files: Readonly<Record<string, string>>;
  edges: readonly ModuleEdge[];
};

/** Only static ES module dependencies are representable. Other loading
 * syntax is refused even inside a function. The reviewed files also contain
 * no await expressions; this restriction includes top-level await. */
export function guardClosure(entry: string, read: (module: string) => Buffer,
    parse: (module: string, text: string) => ts.SourceFile,
    resolve: (from: string, specifier: string) => string | null): GuardClosure | null {
  const files = new Map<string, string>();
  const edges = new Map<string, ModuleEdge>();
  const pending = [entry];
  for (let module = pending.pop(); module !== undefined; module = pending.pop()) {
    if (files.has(module)) continue;
    const bytes = read(module);
    const tree = parse(module, bytes.toString("utf8"));
    files.set(module, createHash("sha256").update(bytes).digest("hex"));
    let refused = false;
    const visit = (n: ts.Node): void => {
      if (ts.isImportEqualsDeclaration(n) || ts.isMetaProperty(n) || ts.isAwaitExpression(n) ||
          (ts.isForOfStatement(n) && n.awaitModifier) ||
          (ts.isCallExpression(n) && n.expression.kind === ts.SyntaxKind.ImportKeyword)) refused = true;
      // Include aliases of these capabilities, not just direct calls. Plain
      // object keys (the scanner's keyword table) do not read a capability.
      if (ts.isIdentifier(n) && ["require", "createRequire", "eval", "Function"].includes(n.text)) refused = true;
      if (ts.isPropertyAssignment(n) && !ts.isComputedPropertyName(n.name)) {
        visit(n.initializer);
        return;
      }
      n.forEachChild(visit);
    };
    visit(tree);
    if (refused) return null;
    for (const s of tree.statements) {
      if (!ts.isImportDeclaration(s) && !ts.isExportDeclaration(s)) continue;
      if (!s.moduleSpecifier) continue;
      if (!ts.isStringLiteral(s.moduleSpecifier) || (ts.isExportDeclaration(s) && s.isTypeOnly)) return null;
      const target = resolve(module, s.moduleSpecifier.text);
      if (target === null) return null;
      pending.push(target);
      const attributes: [string, string][] = [];
      for (const a of s.attributes?.attributes ?? []) {
        if (!ts.isStringLiteral(a.value)) return null;
        attributes.push([a.name.text, a.value.text]);
      }
      attributes.sort(([a], [b]) => a.localeCompare(b));
      const kind = ts.isImportDeclaration(s) ? "import" : "export";
      const add = (local: string, exported: string): void => {
        const edge: ModuleEdge = [module, local, target, exported, attributes, kind];
        edges.set(JSON.stringify(edge), edge);
      };
      if (ts.isImportDeclaration(s)) {
        const clause = s.importClause;
        if (clause?.phaseModifier !== undefined) return null;
        if (!clause) add("", "");
        if (clause?.name) add(clause.name.text, "default");
        const bindings = clause?.namedBindings;
        if (bindings && ts.isNamespaceImport(bindings)) add(bindings.name.text, "*");
        else if (bindings) {
          if (bindings.elements.length === 0) add("", "");
          for (const e of bindings.elements) {
            if (e.isTypeOnly) return null;
            add(e.name.text, e.propertyName?.text ?? e.name.text);
          }
        }
      } else {
        const clause = s.exportClause;
        if (!clause) add("*", "*");
        else if (ts.isNamespaceExport(clause)) add(clause.name.text, "*");
        else {
          if (clause.elements.length === 0) add("", "");
          for (const e of clause.elements) {
            if (e.isTypeOnly) return null;
            add(e.name.text, e.propertyName?.text ?? e.name.text);
          }
        }
      }
    }
  }
  return { files: Object.fromEntries([...files].sort(([a], [b]) => a.localeCompare(b))),
    edges: [...edges].sort(([a], [b]) => a.localeCompare(b)).map(([, e]) => e) };
}
