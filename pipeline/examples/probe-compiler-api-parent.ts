import * as ts from "typescript/unstable/ast";

export function parentKind(sf: ts.SourceFile): number {
  return sf.parent.kind;
}
