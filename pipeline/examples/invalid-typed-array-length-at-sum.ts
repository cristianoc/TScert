// A typed array built at `source.length + 1` read one past its last element:
// `breaks[source.length + 1]!` is `undefined` at `number` (run under Node:
// `pastBreak("ab")` is `undefined`).
export function pastBreak(source: string): number {
  const length = source.length;
  const breaks = new Uint8Array(length + 1);
  return breaks[length + 1]!;
}
