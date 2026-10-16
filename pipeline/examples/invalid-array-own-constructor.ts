// Arrays cannot own constructor, even when an intersection explicitly asks for it.
// The contradictory input contract must be refused rather than verified vacuously.
export function length(xs: number[] & { constructor: Function }): number {
  return xs.length;
}
