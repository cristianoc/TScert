// An unrestricted brand callback cannot acquire a preservation promise by
// being stored in a qualified context. It can pop the outer args during recursion.
import type {
  DeclarationIdentity,
  TypeTerm,
} from "../../tools/declaration-types.mts";
import type { BrandPredicate } from "../../tools/compiler-api.mts";
type Context = { brand: BrandPredicate };
export function branded(
  t: TypeTerm,
  brand: (id: DeclarationIdentity) => boolean,
): TypeTerm {
  const context: Context = { brand };
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
