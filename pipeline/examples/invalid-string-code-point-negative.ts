// A read at a negative position: `text.codePointAt(i - 1)!` at `i === 0` is
// `undefined` at `number`, which the first step returns (run under Node:
// `before("ab")` is `undefined`).
export function before(text: string): number {
  for (let i = 0; i < text.length; i++) {
    const c = text.codePointAt(i - 1)!;
    if (i === 0) return c;
  }
  return 0;
}
