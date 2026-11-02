// Census function: library-globals.mts#errorInstance.
import type { TypeTerm } from "../../tools/declaration-types.mts";
import type { Span } from "../../tools/span.mts";
export function error(span: Span): TypeTerm {
  const text = (name: string) => ({ name, optional: false, readonly: true,
    type: { k: "atom" as const, name: "string" as const, span }, span });
  return { k: "object", fields: [], stringIndex: null, calls: [], span,
    prototype: { k: "object", fields: [text("message"), text("name")], stringIndex: null, calls: [], span } };
}
