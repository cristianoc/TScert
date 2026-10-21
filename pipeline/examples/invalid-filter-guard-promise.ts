// A guard closure passed to `filter` whose body does not establish its
// promise is refused at its promise signature: `x !== undefined` holds of
// `null`, which `filter` then keeps in a result read at `string[]`.
export function strings(xs: (string | null)[]): string[] {
  return xs.filter((x): x is string => x !== undefined);
}
