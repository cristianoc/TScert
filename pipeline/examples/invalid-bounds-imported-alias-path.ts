// Pretext PreparedText: a bound for widths gives no bound for flags.
import type { PreparedText } from '@fixture/bounds-path-types';
/** @requires safeInteger(i) && 0 <= i && i < prepared.widths.length */
export function other(prepared: PreparedText, i: number): number {
  return prepared.flags[i]!;
}
