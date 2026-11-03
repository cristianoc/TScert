// An unannotated constant holding a `flatMap` result is built at the array
// type the first of its uses that expects one expects it at: here a field of
// a record a conditional returns, after a `length` read that expects none, as
// computed-types.mts#typeQuery builds a class value's static fields. Arrays
// are invariant, so the result at the callback's own record types would not
// meet that field's contract.
type Term =
  | { k: "atom"; name: string }
  | {
      k: "ctor";
      params: Term[];
      statics?: { name: string; type: Term; readonly?: true }[];
    };
type Member = { name: string; static: boolean };

export function withStatics(value: Term, members: readonly Member[]): Term {
  if (value.k !== "ctor") return value;
  const statics = members
    .filter((m) => m.static)
    .flatMap((member) => {
      if (member.name === "") return [];
      return [{ name: member.name, type: value }];
    });
  return statics.length ? { ...value, statics } : value;
}
