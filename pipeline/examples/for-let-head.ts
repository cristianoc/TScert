// A `let` in a `for...of` or `for...in` head that nothing assigns is a
// `const`: each iteration binds it afresh, and nothing changes it after.
export function sum(xs: number[]): number {
  let s = 0;
  for (let x of xs) s = s + x;
  return s;
}
export function keys(o: { a: number }): string {
  let r = "";
  for (let k in o) r = r + k;
  return r;
}
