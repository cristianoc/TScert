// A record holding a node is no node (HOST-FAMILIES.md, "Identity through
// program code"): TypeScript refuses the call too, and the pipeline, run past
// TypeScript's errors, refuses it at the call.
import * as ts from "typescript/unstable/ast";

function start(n: ts.Node): number {
  return n.pos;
}

export function boxed(n: ts.Node): number {
  return start({ node: n });
}
