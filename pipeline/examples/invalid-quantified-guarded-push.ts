// Pushing an empty `number[]` onto `(number[] | null)[]` violates
// `forall i in chunks: chunks[i] === null || 1 <= chunks[i].length`, so the
// loop head refuses the back-edge. Unsafe (run under Node: `buildEmpty([1])[0][0]`
// is `undefined` at `number`).

/** @ensures forall i in result: result[i] === null || 1 <= result[i].length */
export function buildEmpty(widths: number[]): (number[] | null)[] {
  const chunks: (number[] | null)[] = [];
  /** @invariant forall i in chunks: chunks[i] === null || 1 <= chunks[i].length */
  for (let i = 0; i < widths.length; i++) {
    const w = widths[i]!;
    if (w <= 0) {
      chunks.push(null);
    } else {
      const row: number[] = [];
      chunks.push(row);
    }
  }
  return chunks;
}
