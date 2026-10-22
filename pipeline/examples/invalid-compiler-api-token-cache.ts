// A source file's `tokenCache`, which the entry point's token functions
// assign on the file they are given, absent before and a `Map` after: its
// reads give no one value for the file's life, so no shape states it
// (COMPILER-API.md, reading rule 1) and its read is refused. Under Node the
// function returns 2: absent at the test, present after the call.
import * as ts from "typescript/unstable/ast";

export function cached(sf: ts.SourceFile, at: number): number {
  if (sf.tokenCache) return 0;
  ts.getTokenAtPosition(sf, at);
  return sf.tokenCache === undefined ? 1 : 2;
}
