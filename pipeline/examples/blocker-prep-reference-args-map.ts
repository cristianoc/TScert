// Census functions:
// compiler-api.mts#hostBrands
// compiler-api.mts#hostBrandsConstructor
// compiler-api.mts#hostBrandsFunction
import type { TypeTerm } from "../../tools/declaration-types.mts";
export function mapped(
  t: Extract<TypeTerm, { k: "reference" }>,
  go: (t: TypeTerm) => TypeTerm,
): TypeTerm {
  return { ...t, args: t.args.map((a) => go(a)) };
}
