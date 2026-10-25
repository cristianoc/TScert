// A loop updating a node to its parent needs the recursive host contract
// preserved across its back edge.
// Census functions:
// fragment-classes.mts#staticInitOf, fragment-support.mts#jumpTarget.
import * as ts from "typescript/unstable/ast";
export function use(node: ts.Node): void {
  let closure = false;
  for (let at: ts.Node = node; at.parent; at = at.parent) {
    if (ts.isFunctionLikeDeclaration(at)) closure = true;
  }
}
