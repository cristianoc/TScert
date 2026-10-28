// A closure calling a compiler node's method, passed to `every`: its object
// is a union of nodes at the closure's own signature and one node at
// `every`'s, and its body reads and binds the member alike at both.
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
