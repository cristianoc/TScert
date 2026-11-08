// No contract gives the result count elements: read(1) is NaN under Node.
export function short(count: number): number[] {
  return [];
}
/** @requires safeInteger(count) && 0 < count */
export function read(count: number): number {
  const out = short(count);
  return out[count - 1]! + 1;
}
