// A module two of whose functions an importer reads: `normalize`, which
// writes nothing, and `measured`, whose search is refused at its cast. A
// module run's refusal at a function of it withdraws that function's read
// alone, so `normalize` is read at its certified footprint.
export function normalize(width: number): number {
  return width <= Infinity ? width : Infinity;
}

export function measured(xs: number[]): number {
  return (xs as unknown as string).length;
}
