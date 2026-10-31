// map callback replacing native method types with unknown.
// Census functions:
// declaration-graph.mts#collect
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
  const nativeFields = fields.map((field) => {
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
  return nativeFields.map((field) =>
    isMethod(field.type)
      ? {
          ...field,
          readonly: true,
          type: { k: "atom" as const, name: "unknown" as const, span },
        }
      : field,
  );
}
