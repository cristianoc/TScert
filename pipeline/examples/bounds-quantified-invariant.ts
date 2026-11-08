// Pretext createLine's flow: each segment's item index names an existing item.
/** @invariant forall i in this.indices: safeInteger(this.indices[i]) && 0 <= this.indices[i] && this.indices[i] < this.widths.length */
type Flow = { widths: number[]; indices: number[] };
export function read(flow: Flow): number {
  let total = 0;
  for (let i = 0; i < flow.indices.length; i++) total += flow.widths[flow.indices[i]!]!;
  return total;
}
export function preserve(flow: Flow): Flow { return flow; }
