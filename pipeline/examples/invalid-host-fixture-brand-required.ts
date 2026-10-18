// A brand is optional (reading rule 2, R6): a node is no value of a type
// requiring it.
import type { Expression } from "@fixture/host";

function branded(x: { readonly _expressionBrand: unknown }): unknown {
  return x._expressionBrand;
}
export function pass(e: Expression): unknown {
  return branded(e);
}
