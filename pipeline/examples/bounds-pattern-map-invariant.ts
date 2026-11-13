// Bounds pattern P20, the supported neighbour of
// `bounds-pattern-map-invariant-refused`: a record returned by its builder.
// Pretext: line-breaks.ts's rule tables.
/** @invariant this.index.length === 4352 */
export type ClassTable = { readonly index: Uint16Array };

function build(): ClassTable {
  const index = new Uint16Array(4352);
  return { index };
}

/** @requires safeInteger(c) && 0 <= c && c < 1114112 */
export function classOfBuilt(c: number): number {
  return build().index[c >> 8]!;
}
