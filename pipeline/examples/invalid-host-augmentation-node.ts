// A member a project's augmentation merges into a host node type: the
// installation's declarations are its whole shape (reading rule 4).
import type * as ts from "typescript/unstable/ast";

export function use(f: ts.SourceFile): number {
  return f.extra;
}
