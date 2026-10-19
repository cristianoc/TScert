// A compiler-API node list is read as a dense readonly array of its elements,
// its own iterator agreeing with indexing (COMPILER-API.md, "Node lists in the
// model"): its spread is an array's, in any position.
import * as ts from "typescript/unstable/ast";

export function parameters(
  node: ts.FunctionDeclaration,
  receiver: boolean,
): readonly ts.ParameterDeclaration[] {
  return receiver ? node.parameters.slice(1) : [...node.parameters];
}
