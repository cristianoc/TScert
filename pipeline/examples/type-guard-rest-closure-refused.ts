// A guard closure collecting a rest array offers its own variadic signature,
// beside which the producer states no promise signature.
export function size(v: unknown): number {
  const isWord = (x: unknown, ...more: unknown[]): x is string =>
    typeof x === "string" && more.length === 0;
  return isWord(v) ? v.length : 0;
}
