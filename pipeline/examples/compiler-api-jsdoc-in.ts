// `"jsDoc" in n` reads no member's value, so it runs no getter and builds
// no array: it is no read of the allocating member. The unit stops at the
// next refusal, a node declaration reaching `NodeArray`, until node lists
// are read.
import * as ts from "typescript/unstable/ast";

export function hasDocs(n: ts.Node): boolean {
  return "jsDoc" in n;
}
