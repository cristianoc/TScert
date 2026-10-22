// A node the package's factory builds: its `parent` is absent, which the
// identifier's shape requires, so the factory is outside the node invariant
// and its values are refused (COMPILER-API.md, R2). Under Node, `made`
// returns `undefined`.
import { createIdentifier } from "typescript/unstable/ast/factory";
import type * as ts from "typescript/unstable/ast";

export function made(): ts.Node {
  return createIdentifier("x").parent;
}
