// Grouped switch cases over a recursive discriminated union meet at their
// shared return, entered from cases of arms whose discriminant type is the
// case's literal.
// Census functions:
// type-term.mts#restRefusal.
import type { TypeTerm } from "../../tools/declaration-types.mts";
export function use(type: TypeTerm): string {
  switch (type.k) {
    case "parameter":
      return "parameter";
    case "binder":
      return "binder";
    case "intersection":
      return "intersection";
    case "tuple":
      return "tuple";
    case "array":
    case "union":
    case "reference":
      return "other";
    default:
      return "default";
  }
}
