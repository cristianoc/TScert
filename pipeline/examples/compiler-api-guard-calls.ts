// Recognition by resolution (HOST-FAMILIES.md, "Calls"): a guard a module of
// the program re-exports narrows as the guard, on both edges; a local
// function named `isIdentifier` is that function, checked by its own body; a
// wrapper of a guard is read at its own signature, so a read after it reads
// a node. pipeline/test.mts forges the false edge's node and the wrapper's
// node at the identifier shape.
import * as ts from "typescript/unstable/ast";
import { isIdentifier as named } from "./compiler-api-guard-reexport.ts";

export function reexported(n: ts.Node): number {
  return named(n) ? n.text.length : 0;
}

export function reexportedOther(n: ts.Node): number {
  return named(n) ? 0 : n.pos;
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

export function wrappedRead(n: ts.Node): number {
  return wrap(n) ? n.pos : 0;
}
