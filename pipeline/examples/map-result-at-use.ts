// An unannotated constant holding a `map` result is built at the array type
// its first use expects: here a field of a returned object literal, as
// type-term.mts's `members` builds a class value's static fields. Arrays are
// invariant, so the result at the callback's own record types would not meet
// that field's contract.
type Field = { name: string; type: number; readonly?: true };
type Term =
  | { k: "constructor"; arity: number; statics?: Field[] }
  | { k: "atom"; name: string };

export function statics(
  only: { k: "constructor"; arity: number },
  fields: { name: string; type: number; readonly: boolean }[],
): Term {
  const statics = fields.map((f) => ({
    name: f.name,
    type: f.type,
    ...(f.readonly ? { readonly: true as const } : {}),
  }));
  return { ...only, statics };
}
