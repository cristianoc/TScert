// A host guard read as its declared `x is T` signature narrows nothing where
// it answers `false`: `node` stays a `BindingName`, whose `Identifier` arm
// has no `elements`. Under the host-guard rule (COMPILER-API.md, guards) the
// call is the test of `node.kind`, which narrows on both edges.
import * as ts from "typescript/unstable/ast";

export function count(node: ts.BindingName): number {
  if (ts.isIdentifier(node)) return 0;
  return node.elements.length;
}
