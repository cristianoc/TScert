import * as ts from "typescript/unstable/ast";

export function parentOf(sf: ts.SourceFile): ts.Node {
  return sf.parent;
}
