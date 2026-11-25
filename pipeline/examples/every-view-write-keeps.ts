// Typed-array byte writes (`Uint8Array`) modify only view spines, so
// quantified array-length and parallel-array invariants on ordinary arrays
// survive across a loop writing a `Uint8Array`.
/**
 * @invariant this.chunks.length === this.flags.length
 * @invariant this.extras === null || this.chunks.length <= this.extras.length
 * @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 * @invariant this.extras === null || forall i in this.chunks: this.chunks[i] === null || this.extras[i] === null || this.chunks[i].length <= this.extras[i].length
 */
type Table = {
  flags: Uint8Array;
  chunks: (number[] | null)[];
  extras: (number[] | null)[] | null;
};

export function markNonNull(table: Table): Table {
  const { flags, chunks } = table;
  for (let i = 0; i < chunks.length; i++) {
    if (chunks[i] !== null) flags[i] = 1;
  }
  return table;
}
