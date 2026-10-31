// A named callback over a compiler node or a record holding its method,
// passed to `every` over nodes. The mixed method invocation requires a
// source-expression typing derivation under the declared parameter union.
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
