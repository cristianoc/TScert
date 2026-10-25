/// <reference lib="esnext.disposable" />
// The named views' contextual query, snapshot enumeration and release,
// and the symbol's stable check flags (COMPILER-API.md, sync member audits).
import type { Expression } from "typescript/unstable/ast";
import type { Checker, Snapshot, Symbol } from "typescript/unstable/sync";

export function contextual(checker: Checker, node: Expression): boolean {
  return checker.getContextualType(node) !== undefined;
}
export function projects(snapshot: Snapshot): number {
  return snapshot.getProjects().length;
}
export function release(snapshot: Snapshot): void {
  snapshot.dispose();
}
export function flags(symbol: Symbol): number {
  return symbol.checkFlags;
}
