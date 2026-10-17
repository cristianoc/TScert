// A nested binding pattern with a default reads the parent's allocating
// member `jsDoc`: refused where it is read.
import * as ts from "typescript/unstable/ast";

export function parentDocumented(n: ts.Node): boolean {
  const {
    parent: { jsDoc: docs = undefined },
  } = n;
  return docs !== undefined;
}
