// A binding pattern reads the allocating member `jsDoc`: refused where it is
// read.
import * as ts from "typescript/unstable/ast";

export function documented(n: ts.Node): boolean {
  const { jsDoc } = n;
  return jsDoc !== undefined;
}
