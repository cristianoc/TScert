// Recognition by resolution (HOST-FAMILIES.md, "Calls"): a guard a module of
// the program re-exports narrows as the guard; a local function named
// `isIdentifier` is that function, checked by its own body; a wrapper of a
// guard is read at its own signature.
import * as ts from "typescript/unstable/ast";
import { isIdentifier as named } from "./compiler-api-guard-reexport.ts";

export function reexported(n: ts.Node): number {
  return named(n) ? n.text.length : 0;
}

function isIdentifier(n: ts.Node): n is ts.Identifier {
  return n.kind === ts.SyntaxKind.Identifier;
}

export function local(n: ts.Node): number {
  return isIdentifier(n) ? n.text.length : 0;
}

function wrap(n: ts.Node): boolean {
  return ts.isIdentifier(n);
}

export function wrapped(n: ts.Node): boolean {
  return wrap(n);
}
