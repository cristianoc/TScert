// Census functions: compiler-api.mts#hostBrands,#hostBrandsFunction,
// #hostBrandsConstructor. A context erases a known brand predicate's footprint.
import type { TypeTerm } from "../../tools/declaration-types.mts";
import type { BrandPredicate } from "../../tools/compiler-api.mts";
type Context = { brand: BrandPredicate };
export function branded(t: TypeTerm): TypeTerm {
  const context: Context = { brand: (id) => id.name === "Host" };
  const go = (
    u: TypeTerm,
  ): Modifies<{ values: "any"; stores: "grow" }, TypeTerm> => {
    if (u.k !== "reference") return u;
    if (context.brand(u.reference.target))
      return { k: "atom", name: "string", span: u.span };
    return { ...u, args: u.args.map((a) => go(a)) };
  };
  return go(t);
}
