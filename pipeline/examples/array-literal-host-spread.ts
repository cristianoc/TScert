// Array literals spreading host iterables and a union of arrays: each is a
// fresh array of its own, whose store contract its claim states, holding the
// elements of `%Spread:K%`'s array; a `Set` built of an array is at the
// array's element type.
export function a(xs: string[]): string[] {
  return [...new Set(xs)];
}
export function b(m: Map<string, number>): string[] {
  return [...m.keys()].filter((k) => k.length > 0);
}
export function c(s: Set<string>): string[] {
  return [...s].map((x) => x.trim());
}
export function d(text: string): string[] {
  return [...text];
}
export function add(
  owners: Map<string, string[]>,
  f: string,
  name: string,
): void {
  owners.set(f, [...(owners.get(f) ?? []), name]);
}
