// A node guard on a value that may be `undefined` throws a `TypeError` there
// (HOST-FAMILIES.md, "Undefined arguments"); its handler receives no
// refinement of the argument, so `parent` there may be absent and returning
// it where a node is promised is refused, though TypeScript accepts it.
// Under Node, `handled` of a source file returns `undefined`.
import * as ts from "typescript/unstable/ast";

export function handled(n: ts.Node): ts.Node {
  try {
    if (ts.isIdentifier(n.parent)) return n;
  } catch {
    return n.parent;
  }
  return n;
}
