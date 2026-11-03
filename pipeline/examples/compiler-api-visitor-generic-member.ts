// Census functions: fragment-statements.mts#statements.
// A recursive visitor whose node a guard and a test of its flags leave at
// several arms of its family, where it calls the node's generic
// `forEachChild` passing itself: each arm holds the member, which the call
// binds to the node, so the visitor is within the footprint its body shows
// and the function meets the footprint it states.
import * as ts from "typescript/unstable/ast";
import type { Node, Statement } from "typescript/unstable/ast";

export function hoistedAt(
  list: readonly Statement[],
): Within<{ value: "any"; store: "grow" }, Node | undefined> {
  const hoisted = (n: Node): Node | undefined => {
    if (
      ts.isFunctionDeclaration(n) ||
      (ts.isVariableDeclarationList(n) &&
        !(n.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const)))
    )
      return n;
    if (ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n))
      return undefined;
    return n.forEachChild(hoisted);
  };
  for (const s of list) {
    const at = hoisted(s);
    if (at) return at;
  }
  return undefined;
}
