// A closure over `Node` passed to a node list of `Expression`s: the
// callback's signature at the element is offered to it, since each
// expression is a node (SOURCE-ELABORATION.md, "Source closures and their
// annotations"). `Expression`'s arms are `Node`'s, its residual within
// `Node`'s by width and depth: a narrower tag, the members `Node`'s
// residual keeps, and a brand `Node`'s lacks. A recursive one, as
// `assignedNames`' `targets`, is offered it through its self entry.
import * as ts from "typescript/unstable/ast";

export function count(root: ts.ArrayLiteralExpression): number {
  let n = 0;
  const one = (e: ts.Node): void => {
    if (ts.isIdentifier(e)) n = n + 1;
  };
  root.elements.forEach(one);
  return n;
}

export function names(root: ts.Node): string[] {
  const out: string[] = [];
  const targets = (e: ts.Node): void => {
    if (ts.isIdentifier(e)) out.push(e.text);
    else if (ts.isArrayLiteralExpression(e)) e.elements.forEach(targets);
  };
  targets(root);
  return out;
}
