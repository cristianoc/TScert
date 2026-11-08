// The code unit after one that starts no pair: a code point at most 0xFFFF
// leaves `i + 1` unbounded by the length, and at the last code unit
// `text.codePointAt(i + 1)!` is `undefined` at `number` (run under Node:
// `next("ab")` is `undefined`).
export function next(text: string): number {
  let x = 0;
  for (let i = 0; i < text.length; i++) {
    if (text.codePointAt(i)! <= 0xffff) x = text.codePointAt(i + 1)!;
  }
  return x;
}
