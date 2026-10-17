// `map` callbacks calling a variadic function with a spread argument: the
// spread reads its array's store in place, and `Math.max` of numbers runs
// no code and writes nothing, so each callback is within the empty
// footprint and the result is dense.
export function peaks(rows: number[][]): number[] {
  return rows.map((row: number[]): number => Math.max(0, ...row));
}

type Box = { values: number[] };
export function boxedPeaks(boxes: Box[]): number[] {
  return boxes.map((b: Box): number => Math.min(...b.values, 100));
}
