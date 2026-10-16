// A key TypeScript types as other than string literals (a `string`, which
// may be `toString` or an array index, a number, a symbol) is the host's
// `%HasProperty%`: whether the object has the property, own or inherited,
// a Boolean that narrows nothing.
export function any(s: string, x: { f: number }): boolean {
  return s in x;
}
export function index(t: [number] | [number, number]): boolean {
  return 1 in t;
}
export function iterable(): boolean {
  return Symbol.iterator in {};
}
