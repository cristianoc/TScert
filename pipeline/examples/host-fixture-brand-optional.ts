// A host member declared `any` is an optional member of type `unknown`
// (reading rule 2): a brand, which no runtime node owns, reads `undefined`.
import type { Expression } from "@fixture/host";

export function brand(e: Expression): unknown {
  return e._expressionBrand;
}
