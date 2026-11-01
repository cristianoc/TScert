// Census functions:
// type-term.mts#oneTerm
import type { TypeTerm } from "../../tools/declaration-types.mts";
type Fn = Extract<TypeTerm, { k: "function" }>;
export function oneTerm(
  terms: Fn[],
  span: [number, number],
): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return terms.length === 1 && terms[0]
    ? terms[0]
    : { k: "intersection", parts: terms, span };
}
