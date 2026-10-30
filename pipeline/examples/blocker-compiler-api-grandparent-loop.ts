// A loop updating a node to its grandparent through a branch a host guard
// refined: the update's entry has its own witness of `at.parent.parent`,
// whose chain of read links includes `at.parent`'s, and the branch's entry
// keeps both, so the update receives the loop test's links of both
// segments (HOST-FAMILIES.md, "Entries").
import * as ts from "typescript/unstable/ast";
export function use(node: ts.Node): boolean {
  let closure = false;
  for (
    let at: ts.Node = node;
    at.parent && at.parent.parent;
    at = at.parent.parent
  ) {
    if (ts.isFunctionLikeDeclaration(at)) closure = true;
  }
  return closure;
}
