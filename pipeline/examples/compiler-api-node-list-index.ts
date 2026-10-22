// A compiler-API node list read at a `number` key is the host's
// `%ElementAt%` over the dense readonly array the model reads it as
// (COMPILER-API.md, "Node lists in the model"): its element at an index
// below the length, else `undefined`. Its last element read at
// `length - 1` is `undefined` for an empty list, and an optional chain
// handles it.
import * as ts from "typescript/unstable/ast";

export function endsWithRest(node: ts.ObjectBindingPattern): boolean {
  const last = node.elements[node.elements.length - 1];
  return last?.dotDotDotToken !== undefined;
}

export function parameterAt(
  node: ts.FunctionDeclaration,
  i: number,
): ts.ParameterDeclaration | undefined {
  return node.parameters[i];
}

export function restName(node: ts.ObjectBindingPattern): string | undefined {
  const last = node.elements[node.elements.length - 1];
  if (last?.dotDotDotToken) {
    const name = last.name;
    if (name && ts.isIdentifier(name)) return name.text;
  }
  return undefined;
}
