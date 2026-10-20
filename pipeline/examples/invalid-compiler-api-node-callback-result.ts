// A callback of `forEachChild` whose result is claimed at a node type it did
// not receive (HOST-FAMILIES.md, "Identity through program code"): its
// argument is any child, so the assertion that it is an `Identifier` has no
// derivation, refused at the assertion. Under Node, on `x + 1;` the first
// child is the binary expression, whose `text` is `undefined`.
import * as ts from "typescript/unstable/ast";

const claim = (c: ts.Node): ts.Identifier => c as ts.Identifier;

export function firstName(n: ts.Node): string {
  const found = n.forEachChild(claim);
  return found === undefined ? "" : found.text;
}
