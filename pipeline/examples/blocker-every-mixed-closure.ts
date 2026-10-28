// A closure calling a method of an object that is a compiler node or a
// record holding the method as a field, passed to `every` over nodes: its
// body is read and called in one step dispatched on the object at the
// closure's own signature, where the record's field is no host member, and
// as one node's bound member at `every`'s, so it lowers differently under
// the two signatures.
import * as ts from "typescript/unstable/ast";

interface Located {
  getSourceFile: () => ts.SourceFile;
}

export function allLibrary(
  libraryFile: (file: ts.SourceFile) => boolean,
  parts: readonly ts.InterfaceDeclaration[],
): boolean {
  const isLibrary = (node: ts.Node | Located): boolean =>
    libraryFile(node.getSourceFile());
  return parts.every(isLibrary);
}
