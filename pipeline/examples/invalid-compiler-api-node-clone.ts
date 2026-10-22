// A clone the entry point builds: its root keeps no `parent`, which a
// variable declaration's shape requires, so the clone functions are outside
// the node invariant and their values are refused (COMPILER-API.md, R2).
// Under Node, `cloneParent` returns `undefined`.
import * as ts from "typescript/unstable/ast";

export function cloneParent(d: ts.VariableDeclaration): ts.Node {
  return ts.getSynthesizedDeepClone(d).parent;
}
