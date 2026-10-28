// `Object.entries` of a dictionary, where TypeScript selects the generic
// overload, and of an interface's object and a writable array, where it
// selects the plain one at `{}` and the generic one at `ArrayLike<T>`: the
// overloads a module's calls choose are one callee, and each call is checked
// at the overload its operand meets. A dictionary's every own string key
// holds a `T`; an invariant field and a writable array exclude host values.
interface R {
  a: number;
}
export function total(d: { readonly [k: string]: number }): number {
  let s = 0;
  for (const [, v] of Object.entries(d)) s += v;
  return s;
}
export function count(r: R, xs: number[]): number {
  const rs: [string, unknown][] = Object.entries(r);
  const ps: [string, unknown][] = Object.entries(xs);
  return rs.length + ps.length;
}
