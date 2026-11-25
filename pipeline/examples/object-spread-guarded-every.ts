// Object spread `{ ...p, extra }` preserves guarded and quantified invariants
// on every non-overridden key of `p`.
/** @invariant this.extras === null || this.widths.length <= this.extras.length
 *  @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 *  @invariant this.chunkExtras === null || forall i in this.chunks: this.chunks[i] === null || this.chunkExtras[i] === null || this.chunks[i].length <= this.chunkExtras[i].length
 */
type Base = {
  widths: number[];
  extras: number[] | null;
  chunks: (number[] | null)[];
  chunkExtras: (number[] | null)[] | null;
};
type Extended = Base & { extra: number };

export function extend(p: Base, extra: number): Extended {
  const result = { ...p, extra };
  return result;
}

/** @requires safeInteger(i) */
export function readFirstChunk(p: Extended, i: number): number {
  if (i < 0 || i >= p.chunks.length) return 0;
  const c = p.chunks[i];
  if (c === undefined || c === null) return 0;
  return c[0]!;
}
