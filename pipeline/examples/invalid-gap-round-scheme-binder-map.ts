// map callback allocating a generic signature's type-parameter record.
// Census functions:
// declaration-graph.mts#selectGlobal
import type { TypeTerm } from "../../tools/declaration-types.mts";
export function scheme(
  names: readonly string[],
  at: [number, number],
): TypeTerm {
  const scheme: Extract<TypeTerm, { k: "scheme" }> = {
    k: "scheme",
    signatures: [],
    span: at,
    binders: names.map((name) => {
      const binder = {
        name,
        bound: null,
        resolution: null,
        default: null,
        span: at,
      };
      return binder;
    }),
  };
  return scheme;
}
