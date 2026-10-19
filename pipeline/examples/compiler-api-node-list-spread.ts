// A compiler-API node list is a subclass of `Array`, iterated by
// `Array.prototype`'s iterator over its store (COMPILER-API.md, "Node lists"):
// its spread is an array's, in any position.
import * as ts from "typescript/unstable/ast";

export function parameters(
  node: ts.FunctionDeclaration,
  receiver: boolean,
): readonly ts.ParameterDeclaration[] {
  return receiver ? node.parameters.slice(1) : [...node.parameters];
}
