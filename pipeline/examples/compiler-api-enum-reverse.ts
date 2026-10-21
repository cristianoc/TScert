// The compiler API's `SyntaxKind`, read at a node's kind: the object Node
// loads holds, at each member's value, the name of a member with that value
// (C1), so the read is a string. The project checks indexed reads
// (`noUncheckedIndexedAccess`), so TypeScript adds `undefined`.
import * as ts from "typescript/unstable/ast";
import type { Statement } from "typescript/unstable/ast";

export function kindName(s: Statement): string | undefined {
  return ts.SyntaxKind[s.kind];
}

export function isDeclarationStatement(s: Statement): boolean {
  const name: string = ts.SyntaxKind[s.kind] ?? "";
  return name.endsWith("Declaration");
}

export function identifierName(): string | undefined {
  return ts.SyntaxKind[ts.SyntaxKind.Identifier];
}
