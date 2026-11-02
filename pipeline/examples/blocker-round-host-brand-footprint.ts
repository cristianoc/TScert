// Census functions: compiler-api.mts#hostBrands,#hostBrandsFunction,
// #hostBrandsConstructor. A context erases a known brand predicate's footprint.
import type {
  DeclarationIdentity,
  TypeTerm,
} from "../../tools/declaration-types.mts";
type Context = { brand: (id: DeclarationIdentity) => boolean };
export function branded(t: TypeTerm): TypeTerm {
  const context: Context = { brand: (id) => id.name === "Host" };
  const go = (u: TypeTerm): TypeTerm => {
    if (u.k !== "reference") return u;
    if (context.brand(u.reference.target))
      return { k: "atom", name: "string", span: u.span };
    return { ...u, args: u.args.map((a) => go(a)) };
  };
  return go(t);
}
