// A spread of a node list or a set, `...(n.typeArguments ?? new Set())`: the
// set is no array store, and its iterator is no array's, so the spread of the
// union has no element sequence to pass.
import * as ts from "typescript/unstable/ast";

export function keys(out: ts.TypeNode[], node: ts.TypeReferenceNode): void {
  out.push(...(node.typeArguments ?? new Set<ts.TypeNode>()));
}
