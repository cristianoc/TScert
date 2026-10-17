// A node's `jsDoc` builds a fresh array on each read, so two reads give
// different arrays: a host member whose read allocates is refused where it
// is read.
import * as ts from "typescript/unstable/ast";

export function documented(n: ts.Node): boolean {
  const docs = n.jsDoc;
  return docs !== undefined;
}
