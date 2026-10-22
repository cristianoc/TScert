// A node list's last element read at `length - 1` is `undefined` for an
// empty list, as for `const {} = o`'s pattern: the assertion that it is an
// element does not make it one (run under Node).
import * as ts from "typescript/unstable/ast";

export function lastElement(node: ts.ObjectBindingPattern): ts.BindingElement {
  return node.elements[node.elements.length - 1]!;
}
