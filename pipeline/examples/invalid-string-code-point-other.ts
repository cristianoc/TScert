// A read of `b` below another string's length: `b.codePointAt(i)!` at
// `i < a.length` is `undefined` at `number` where `b` is shorter (run under
// Node: `other("ab", "")` is `undefined`).
export function other(a: string, b: string): number {
  let x = 0;
  for (let i = 0; i < a.length; i++) x = b.codePointAt(i)!;
  return x;
}
