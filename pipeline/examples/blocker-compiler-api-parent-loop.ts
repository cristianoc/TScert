// A loop updating a node to its parent through a branch a host guard
// refined: the guard's arms state `parent` required, which implies the
// loop test's refinement of `at.parent`, and the branch's entry keeps the
// path's witness, so the update receives the test's read link
// (HOST-FAMILIES.md, "Entries").
// Census functions:
// fragment-classes.mts#staticInitOf, fragment-support.mts#jumpTarget.
import * as ts from "typescript/unstable/ast";
export function use(node: ts.Node): void {
  let closure = false;
  for (let at: ts.Node = node; at.parent; at = at.parent) {
    if (ts.isFunctionLikeDeclaration(at)) closure = true;
  }
}
