// A dictionary holds no prototype, so a key `in` finds on it is its own: the
// read is at the index type, without `undefined`.
export function present(x: { [f: string]: number }): number {
  if ("a" in x) {
    return x.a;
  }
  return 0;
}
export function readonlyIndex(x: { readonly [f: string]: string }): string {
  return "b" in x ? x.b : "";
}
