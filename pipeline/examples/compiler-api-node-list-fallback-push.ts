// A spread of a node list or a fresh empty array, `...(n.typeArguments ?? [])`,
// into an array's `push`: each alternative is an array store the standard
// array iterator reads, the node list's elements at its element type and the
// empty array's none, so the actuals are the node list's elements.
// Census functions: fragment-parse.mts#lowerFile, fragment-parse.mts#parseModules,
// fragment-parse.mts#lowerModule, fragment-parse.mts#parseFragment,
// fragment-parse.mts#diagnosticFragment, fragment-parse.mts#parseFile.
import * as ts from "typescript/unstable/ast";

export function keys(out: ts.TypeNode[], node: ts.TypeReferenceNode): void {
  out.push(...(node.typeArguments ?? []));
}
