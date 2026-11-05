// A map callback returning a record types its literal at the expected
// discriminated result type.
// Census functions:
// type-term.mts#emptyObject.
import type { TypeTerm } from "../../tools/declaration-types.mts";
export function use(
  span: [number, number],
): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return {
    k: "union",
    span,
    parts: (["boolean", "number"] as const).map((name) => ({
      k: "atom",
      name,
      span,
    })),
  };
}
