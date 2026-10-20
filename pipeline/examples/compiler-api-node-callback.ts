// A callback of `forEachChild`, the package's generic method, reading its
// node argument's members (HOST-FAMILIES.md, "Identity through program
// code"): its argument is a node, as the audited contract of the function
// passing it states; the binder is instantiated at the callback's result,
// `undefined` among it. A callback returning its argument returns the node it
// received, and a guard names the identifier shape the forged claims of
// pipeline/test.mts reuse.
import * as ts from "typescript/unstable/ast";

const start = (c: ts.Node): number | undefined =>
  c.pos > 0 ? c.pos : undefined;

export function firstChild(n: ts.Node): number {
  return n.forEachChild(start) ?? 0;
}

const self = (c: ts.Node): ts.Node => c;

export function firstNode(n: ts.Node): ts.Node | undefined {
  return n.forEachChild(self);
}

export function name(n: ts.Node): string {
  return ts.isIdentifier(n) ? n.text : "";
}
