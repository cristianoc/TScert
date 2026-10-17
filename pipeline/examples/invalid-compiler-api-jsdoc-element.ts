// `n["jsDoc"]` reads the same allocating member as `n.jsDoc`: refused where
// it is read.
import * as ts from "typescript/unstable/ast";

export function documented(n: ts.Node): boolean {
  return n["jsDoc"] !== undefined;
}
