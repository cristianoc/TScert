// pretext line-text.ts getGraphemeEnds: a cache insertion keeps the view
// in prepared.segmentFlags and its stable length through the field.
/** @invariant this.segmentFlags.length === this.widths.length */
export type Prepared = { widths: number[]; segmentFlags: Uint8Array };

export function remember(
  prepared: Prepared,
  cache: Map<number, number>,
): number {
  cache.set(0, 1);
  return prepared.widths.length;
}

export function fill(prepared: Prepared): number {
  prepared.segmentFlags.fill(1);
  return prepared.widths.length;
}

export function replace(prepared: { segmentFlags: Uint8Array }): void {
  prepared.segmentFlags = new Uint8Array(0);
}
