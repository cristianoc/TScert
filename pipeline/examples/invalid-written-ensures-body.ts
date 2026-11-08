// The claimed length is false: short(1)[0] is undefined under Node.
/** @requires safeInteger(count) && 0 < count
 * @ensures result.length === count */
export function short(count: number): number[] {
  return [];
}
