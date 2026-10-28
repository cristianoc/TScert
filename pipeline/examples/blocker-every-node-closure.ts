// A closure calling a compiler node's method, passed to `every`: its body
// lowers differently under one of the signatures it is claimed at. Called
// directly, or passed to `every` without the method call, it verifies.
// Census functions:
// array-prototype.mts#mergeRefusal, array-prototype.mts#prototype,
// array-prototype.mts#arrayPrototype, array-prototype.mts#primitivePrototype.
import * as ts from "typescript/unstable/ast";

export function allLibrary(
  libraryFile: (file: ts.SourceFile) => boolean,
  parts: readonly ts.InterfaceDeclaration[],
): boolean {
  const isLibrary = (node: ts.Node): boolean =>
    libraryFile(node.getSourceFile());
  return parts.every(isLibrary);
}
