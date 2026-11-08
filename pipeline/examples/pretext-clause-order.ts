// Pretext setEmptyObjectFacts/setupClusterBoundaries: adjacent boundaries.
/**
 * @requires safeInteger(index) && 0 <= index && index + 1 < xs.length
 * @requires forall i in xs: safeInteger(xs[i]) && 0 <= xs[i] && xs[i] < values.length
 * @requires forall i in xs: i + 1 >= xs.length || (safeInteger(xs[i]) && safeInteger(xs[i + 1]) && xs[i] <= xs[i + 1])
 */
export function ordered(xs: number[], values: number[], index: number): number {
  return values[xs[index + 1]! - xs[index]!]!;
}
