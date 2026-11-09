// Census functions:
// type-term.mts#oneTerm
import type { TypeTerm } from "../../tools/declaration-types.mts";
type Fn = Extract<TypeTerm, { k: "function" }>;
export function oneTerm(
  terms: Fn[],
  span: [number, number],
): Modifies<{ values: "any"; stores: "grow" }, TypeTerm> {
  const [only] = terms;
  if (terms.length === 1 && only) return only;
  const parts: TypeTerm[] = terms.map((term): TypeTerm => term);
  return { k: "intersection", parts, span };
}
