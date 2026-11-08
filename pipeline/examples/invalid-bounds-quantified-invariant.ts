// A flow constructor must establish every element bound of its result.
/** @invariant forall i in this.indices: safeInteger(this.indices[i]) && 0 <= this.indices[i] && this.indices[i] < this.widths.length */
type Flow = { widths: number[]; indices: number[] };
export function broken(): Flow { return { widths: [1], indices: [1] }; }
