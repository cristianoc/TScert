// Template interpolation after printing a nullable receiver field.
// Census functions:
// shadow-contracts.mts#print
// shadow-contracts.mts#printSignature
// shadow-contracts.mts#statedSignatures
// shadow-contracts.mts#prelude
// shadow-contracts.mts#shadowText
import type { TypeTerm } from "../../tools/declaration-types.mts";
function print(term: TypeTerm): string | null {
  return term.k === "binder" ? term.name : null;
}
export function signature(term: Extract<TypeTerm, { k: "function" }>): string {
  const receiver = term.receiver && print(term.receiver);
  if (term.receiver && receiver === null) return "";
  return receiver
    ? `(this: ${receiver}${term.params.length || term.rest ? ", " : ""}`
    : "()";
}
