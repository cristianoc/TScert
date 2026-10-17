// An optional chain reads the allocating member `jsDoc` where the node is
// present: refused where it is read.
import * as ts from "typescript/unstable/ast";

export function documented(n: ts.Node | undefined): boolean {
  return n?.jsDoc !== undefined;
}
