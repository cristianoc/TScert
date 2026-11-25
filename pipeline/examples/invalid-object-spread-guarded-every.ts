// Object spread `{ ...p, chunkExtras: [[]] }` overrides `chunkExtras` and does
// not preserve the quantified parallel-length invariant from `p`.
/** @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length
 *  @invariant this.chunkExtras === null || forall i in this.chunks: this.chunks[i] === null || this.chunkExtras[i] === null || this.chunks[i].length <= this.chunkExtras[i].length
 */
type Base = {
  chunks: (number[] | null)[];
  chunkExtras: (number[] | null)[] | null;
};
type Extended = Base & { extra: number };

export function extendBroken(p: Base, extra: number): Extended {
  const result = { ...p, chunkExtras: [[]], extra };
  return result;
}
