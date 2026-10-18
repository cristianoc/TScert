// The sync API's classes, and its `Type`, read through their named views
// (COMPILER-API.md, reading rule 4): the members the contract lists, each as
// its reviewed declaration states it.
import * as ts from "typescript/unstable/ast";
import type { Checker, Symbol } from "typescript/unstable/sync";

export function flagsOf(checker: Checker, n: ts.Node): number {
  const t = checker.getTypeAtLocation(n);
  return t === undefined ? 0 : t.flags;
}

export function nameOf(checker: Checker, n: ts.Node): string {
  const s: Symbol | undefined = checker.getSymbolAtLocation(n);
  return s === undefined ? "" : s.name;
}
