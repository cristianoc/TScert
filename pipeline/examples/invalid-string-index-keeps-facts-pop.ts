// A coalescing read whose right operand pops an array: the string's index
// read writes nothing, but the `pop` does, and `xs.length === ys.length`
// does not survive the statement. Under Node, `lastAfter("", [1], [2])`
// pops `ys` and reads `ys[0]`, `undefined` at `number`.

/** @requires xs.length === ys.length && 1 <= xs.length */
export function lastAfter(text: string, xs: number[], ys: number[]): number {
  const c = text[0] ?? String(ys.pop());
  return c === "" ? 0 : ys[xs.length - 1]!;
}
