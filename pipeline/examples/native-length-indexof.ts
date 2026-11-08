// Pretext: measurement.ts#getSegmentFit, bounds of a searched position.
export function found(xs: string[], value: string): string {
  const at = xs.indexOf(value);
  return at >= 0 ? xs[at]!.toUpperCase() : "absent";
}
