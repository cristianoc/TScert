// A loop updating a node to its parent, whose body writes the root in the
// branch a host guard refined: the write ends the read link of the loop's
// test, so the update's read of `parent` is at the declared read, which may
// be `undefined` (a source file has no parent), and the slot's `Node`
// contract is not established (HOST-FAMILIES.md, "Paths rooted at a slot").
import * as ts from "typescript/unstable/ast";
export function use(node: ts.Node, other: ts.Node): void {
  for (let at: ts.Node = node; at.parent; at = at.parent) {
    if (ts.isFunctionLikeDeclaration(at)) {
      at = other;
    }
  }
}
