// A loop reading code points up to and including the length: its last read,
// `text.codePointAt(i)!` at `i === text.length`, is `undefined` at `number`,
// which `x` returns (run under Node: `last("ab")` is `undefined`).
export function last(text: string): number {
  let x = 0;
  for (let i = 0; i <= text.length; i++) x = text.codePointAt(i)!;
  return x;
}
