// A user guard is read at its own certified promise, which the extension
// for family guards on `undefined` (HOST-FAMILIES.md, "Undefined
// arguments") leaves as it is: `absent`'s `true` holds of `undefined`, so
// `n.parent` keeps it on that edge and returning it where a node is
// promised is refused, though TypeScript accepts it. Under Node, `parentOf`
// of a source file returns `undefined`.
import * as ts from "typescript/unstable/ast";

function absent(x: unknown): x is undefined {
  return typeof x === "undefined";
}

export function parentOf(n: ts.Node): ts.Node {
  if (absent(n.parent)) return n.parent;
  return n;
}
