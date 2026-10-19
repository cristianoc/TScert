// Family identity follows the program's own code (HOST-FAMILIES.md, "Identity
// through program code"): a program alias and a re-export of `Node` are the
// family type, a generic identity at a node type returns its node, a
// verified wrapper returns its node argument, a record holding a node reads
// its field as the node, and a method every arm of the run's `Node` shares is
// called on it.
import * as ts from "typescript/unstable/ast";
import type { Tree } from "@fixture/node-types";

type N = ts.Node;

function same<T>(x: T): T {
  return x;
}

function wrap(n: ts.Node): ts.Node {
  return n;
}

export function aliased(n: N): Tree {
  return n;
}

export function generic(n: ts.Identifier): ts.Identifier {
  return same(n);
}

export function genericNode(n: ts.Node): ts.Node {
  return same(n);
}

export function wrapped(n: ts.Node): number {
  return wrap(n).pos;
}

export function held(n: ts.Node): ts.Node {
  const box = { node: n };
  return box.node;
}

export function text(n: ts.Node): string {
  return n.getText();
}
