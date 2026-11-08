// Pretext layout's PreparedText path clauses follow an imported intersection alias.
import type { PreparedText } from '@fixture/bounds-path-types';
/** @requires safeInteger(i) && 0 <= i && i < prepared.widths.length */
export function widthAt(prepared: PreparedText, i: number): number {
  return prepared.widths[i]!;
}
/** @ensures safeInteger(result) && result === prepared.widths.length */
export function size(prepared: PreparedText): number {
  return prepared.widths.length;
}
export function first(prepared: PreparedText): number {
  return prepared.widths.length > 0 ? widthAt(prepared, 0) : 0;
}
