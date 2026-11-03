// The guard keeping the found fields with its parameter inferred: the
// producer claims the parameter at the arms of `TypeTerm | null`, and does
// not select `filter`'s guard signature, so the result is claimed at the
// element type with `null` and does not meet `union`'s `TypeTerm[]`.
// `blocker-last-indexed-access-fields` names the parameter's type.
// Census functions: computed-types.mts#indexedAccess.
import type { TypeTerm } from "../../tools/declaration-types.mts";

type ObjectTerm = Extract<TypeTerm, { k: "object" }>;

const union = (parts: TypeTerm[]): TypeTerm => {
  const [only] = parts;
  return parts.length === 1 && only ? only : { k: "union", parts, span: [0, 0] };
};

export function fields(object: ObjectTerm, keys: TypeTerm[]): TypeTerm | null {
  const parts = keys.map((key) => {
    if (key.k !== "literal" || key.name !== "string") return null;
    const field = object.fields.find((f) => f.name === key.text);
    return field ? field.type : null;
  });
  const found = parts.filter((p): p is TypeTerm => p !== null);
  return found.length === parts.length ? union(found) : null;
}
