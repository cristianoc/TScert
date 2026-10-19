// A listed guard used as a value (HOST-FAMILIES.md, "Guards as values"):
// read at its entry's signature, which changes no value and no store and
// promises the family's shapes at its tag set, so it meets a parameter of
// the guard type its declaration states, and a call of a name holding it
// narrows the argument on its `true` edge.
import * as ts from "typescript/unstable/ast";

function count(nodes: readonly ts.Node[], test: (n: ts.Node) => n is ts.Identifier): number {
  let total = 0;
  for (const n of nodes) if (test(n)) total += n.text.length;
  return total;
}

export function names(nodes: readonly ts.Node[]): number {
  return count(nodes, ts.isIdentifier);
}

export function stored(node: ts.Node): number {
  const g = ts.isIdentifier;
  if (g(node)) return node.text.length;
  return node.pos;
}

export function anyName(nodes: readonly ts.Node[]): boolean {
  return nodes.some((n) => ts.isIdentifier(n));
}

export function identifiers(nodes: readonly ts.Node[]): number {
  return nodes.filter(ts.isIdentifier).length;
}
