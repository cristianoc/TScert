// Publishing a FunctionTerm array as writable TypeTerm storage lets the
// returned intersection replace a function through the original alias.
import type { TypeTerm } from "../../tools/declaration-types.mts";
type Fn = Extract<TypeTerm, { k: "function" }>;
export function oneTerm(
  terms: Fn[],
  span: [number, number],
): Modifies<{ values: "any"; stores: "grow" }, TypeTerm> {
  return terms.length === 1 && terms[0]
    ? terms[0]
    : { k: "intersection", parts: terms, span };
}
