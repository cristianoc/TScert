// An assignment pattern reads the allocating member `jsDoc` of its source:
// refused where it is read.
import * as ts from "typescript/unstable/ast";

export function documented(n: ts.Node): boolean {
  let docs: readonly ts.Node[] | undefined = undefined;
  ({ jsDoc: docs } = n);
  return docs !== undefined;
}
