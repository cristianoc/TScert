// Native method maps with explicit writable field contracts.
// Equivalent form used by declaration-graph.mts#collect; no remaining census sites.
import type { TypeTerm, PropertyKey } from "../../tools/declaration-types.mts";
import type { Span } from "../../tools/span.mts";
type Field = {
  name: PropertyKey;
  optional: boolean;
  readonly: boolean;
  type: TypeTerm;
  span: Span;
};
export function native(fields: readonly Field[], span: Span): Field[] {
  const nativeFields = fields.map((field): Field => {
    if (field.name !== "finally") return field;
    const updated: TypeTerm = {
      k: "scheme",
      span,
      binders: [],
      signatures: [],
    };
    return { ...field, readonly: true, type: updated };
  });
  const isMethod = (type: TypeTerm): boolean =>
    (type.k === "scheme" &&
      type.signatures.every(
        (signature) =>
          signature.k === "function" && signature.receiver?.k === "self",
      )) ||
    (type.k === "function" && type.receiver?.k === "self") ||
    (type.k === "intersection" && type.parts.every(isMethod));
  return nativeFields.map((field): Field => {
    if (!isMethod(field.type)) return field;
    const type: TypeTerm = { k: "atom", name: "unknown", span };
    return { ...field, readonly: true, type };
  });
}
