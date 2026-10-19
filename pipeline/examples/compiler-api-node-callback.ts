// A callback of `forEachChild`, the package's generic method, reading its
// node argument's members: the call of a generic method on a node is
// refused (WORK.md, family identity controls).
import * as ts from "typescript/unstable/ast";

const start = (c: ts.Node): number | undefined => (c.pos > 0 ? c.pos : undefined);

export function firstChild(n: ts.Node): number {
  return n.forEachChild(start) ?? 0;
}
