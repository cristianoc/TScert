// A request of the sync API changes no location of the program but through
// its instance's retained `fs` callbacks, each within
// `{value: any, store: grow}` (T6, COMPILER-API.md, "The sync API"): a `map`
// callback calling the checker removes no array element, so the result is
// dense.
import type { Node } from "typescript/unstable/ast";
import type { Checker } from "typescript/unstable/sync";

export function flags(checker: Checker, nodes: Node[]): number[] {
  const r: number[] = nodes.map(
    (n) => checker.getTypeAtLocation(n)?.flags ?? 0,
  );
  return r;
}
