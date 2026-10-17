// The compiler API's enums the contract lists, read as values: each member
// at its declared value's literal type. In the file's own annotations an
// enum member names its literal, and the enum its members' union.
import * as ts from "typescript/unstable/ast";
import {
  DiagnosticCategory,
  SymbolFlags,
  TypeFlags,
  type Diagnostic,
} from "typescript/unstable/sync";

export function isIdentifierKind(kind: number): boolean {
  return kind === ts.SyntaxKind.Identifier;
}

export function unionFlag(): number {
  return TypeFlags.Union;
}

export function aliasOrConst(): number[] {
  return [SymbolFlags.Alias, ts.NodeFlags.Const];
}

export function identifierKind(): ts.SyntaxKind.Identifier {
  return ts.SyntaxKind.Identifier;
}

export function someKind(): ts.SyntaxKind {
  return ts.SyntaxKind.SourceFile;
}

// A host field of an enum type is a number: a `switch` over it completes
// through its default.
export function severity(d: Diagnostic): string {
  switch (d.category) {
    case DiagnosticCategory.Error:
      return "error";
    default:
      return "other";
  }
}

// The file's own declarations name the namespace's enum members too.
interface Marked {
  readonly kind: ts.SyntaxKind.Identifier;
}
const ACCESS: ts.SyntaxKind.PublicKeyword[] = [ts.SyntaxKind.PublicKeyword];

export function markedKind(m: Marked): number {
  return m.kind + ACCESS.length;
}
