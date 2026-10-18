// A member of a host class its view does not list is no member of the class
// as the contract reads it (COMPILER-API.md, reading rule 4, L6).
import * as ts from "typescript/unstable/ast";
import type { Checker } from "typescript/unstable/sync";

export function base(checker: Checker, n: ts.Node): number {
  const t = checker.getTypeAtLocation(n);
  return t === undefined ? 0 : checker.getBaseTypes(t).length;
}
