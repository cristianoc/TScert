// An overload of a host member its view does not list (the array form of
// `getTypeOfSymbol`) is no signature of the member as the contract reads it
// (reading rule 4).
import type { Checker, Symbol } from "typescript/unstable/sync";

export function many(checker: Checker, a: Symbol, b: Symbol): boolean {
  const types = checker.getTypeOfSymbol([a, b]);
  return Array.isArray(types);
}
