// An intersection of records with readonly fields is one object under every
// conjunct: its invariant fields stay writable and its readonly fields are
// views, read at their types.
export function merged(
  value: { readonly value: number } & { readonly tag: "ok" },
): { readonly value: number; readonly tag: "ok" } {
  return value;
}
export function mixed(
  v: { a: number; readonly c: number } & { readonly b: number },
): number {
  v.a = v.b;
  return v.a + v.c;
}
