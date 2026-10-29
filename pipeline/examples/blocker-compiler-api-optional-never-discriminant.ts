// A test that an optional `never` field is undefined drops the arm whose
// field is a compiler node or null: a node is no `undefined`, also where
// the kinds the program tests make `Node` a union some of whose arms are
// intersections (`Token<…> & KeywordExpression<…>`).
// Census functions:
// written-applications.mts#writtenApplications.
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";
export function keyword(n: Node): string {
  switch (n.kind) {
    case ts.SyntaxKind.NullKeyword: return "null";
    case ts.SyntaxKind.StringKeyword: return "string";
    default: return "";
  }
}
export function names(roots: readonly Node[]): Node[] {
  type Determined = { nodes: Node[]; inferred?: never } | { inferred: Node | null };
  const all = (parts: readonly Determined[]): Determined => {
    const nodes: Node[] = [];
    for (const part of parts) {
      if (part.inferred !== undefined) return part;
      nodes.push(...part.nodes);
    }
    return { nodes };
  };
  const found = all([{ nodes: [...roots] }]);
  return found.inferred !== undefined ? [] : found.nodes;
}
