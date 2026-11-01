// Census functions:
// declaration-graph.mts#promisedBinders
// declaration-graph.mts#promisedMethods
import type { TypeTerm } from "../../tools/declaration-types.mts";
export function binders<B extends { name: string; bound: TypeTerm | null }>(
  bs: B[],
  term: TypeTerm,
): B[] {
  return bs.map((b) =>
    b.bound === null
      ? b
      : {
          ...b,
          bound: {
            k: "intersection",
            span: b.bound.span,
            parts: [b.bound, term],
          },
        },
  );
}
