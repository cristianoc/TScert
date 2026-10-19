// Spreads of a value whose type is a binder bounded by a record, or an
// intersection of records: the copy takes the operand's own enumerable
// properties, which its bound's fields state, so it is a record of those
// fields, and of the ones written after.
type Binder = { name: string; bound: number | null };
export function bounded<B extends Binder>(b: B): Binder {
  return { ...b, bound: 1 };
}
export function unbounded<B extends Binder>(
  b: B,
): { name: string; bound: number } {
  return { ...b, bound: 0 };
}
export function others<B extends Binder>(b: B): { bound: number | null } {
  const { name, ...rest } = b;
  return rest;
}
export function spanned(b: Binder & { span: number }): {
  name: string;
  bound: number;
  span: number;
} {
  return { ...b, bound: 1 };
}
// A field of the union arm the literal builds is built at that arm's type:
// `map` at the array the arm's field holds.
type Term =
  | { k: "scheme"; binders: (Binder & { span: number })[] }
  | { k: "atom" };
export function rebound(t: Term): Term {
  if (t.k === "scheme")
    return { ...t, binders: t.binders.map((b) => ({ ...b, bound: 1 })) };
  return t;
}
