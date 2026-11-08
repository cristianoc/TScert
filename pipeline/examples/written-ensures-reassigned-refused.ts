/** @ensures safeInteger(count) && result.length === count */
export function reassigned(count: number): number[] {
  count = 0;
  return [];
}
