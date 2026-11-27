// One mutable field cannot simultaneously hold a closed record for a readonly
// index-signature view and an open record for a mutable writer: writing an open
// object `{ a: 2, extra: "boom" }` through the mutable alias exposes a string
// where the readonly dictionary expects a number.
export function unsoundAliasedWrite(openRec: { a: number }): number {
  const box = { inner: { a: 1 } };
  const mut: { inner: { a: number } } = box;
  const ro: { readonly inner: { readonly [k: string]: number } } = box;
  mut.inner = openRec;
  const v = ro.inner["extra"];
  return v !== undefined ? v : 0;
}
