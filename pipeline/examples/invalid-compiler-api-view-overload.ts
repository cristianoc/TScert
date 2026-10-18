// An overload of a host member its view does not list (the array form of
// `getTypeAtLocation`) is no signature of the member as the contract reads
// it (reading rule 4).
import * as ts from "typescript/unstable/ast";
import type { Checker } from "typescript/unstable/sync";

export function many(checker: Checker, a: ts.Node, b: ts.Node): boolean {
  const types = checker.getTypeAtLocation([a, b]);
  return Array.isArray(types);
}
