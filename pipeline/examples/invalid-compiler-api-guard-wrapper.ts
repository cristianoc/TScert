// A wrapper of a listed guard is an ordinary function, read at its own
// signature (HOST-FAMILIES.md, "Calls"): its `boolean` narrows nothing, so
// `n` is no `Identifier` where it answers `true`: refused at the assertion.
import * as ts from "typescript/unstable/ast";

function wrap(n: ts.Node): boolean {
  return ts.isIdentifier(n);
}

export function wrapped(n: ts.Node): number {
  return wrap(n) ? (n as ts.Identifier).text.length : 0;
}
