// A family guard that cannot hold of its actual's type, on a parameter the
// function assigns, so it is an ordinary call at its promise signature:
// `OmittedExpression` and `BindingElement` fix `kind` at two literals, so the
// promise filtered by `e`'s type is empty and the `true` branch is reached by
// no environment (PROGRAM-TYPING.md, "Refinement by a fact").
import * as ts from "typescript/unstable/ast";

export function f(e: ts.BindingElement, next: ts.BindingElement): number {
  const omitted = ts.isOmittedExpression(e) ? 1 : 0;
  e = next;
  return omitted + e.pos;
}
