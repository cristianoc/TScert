// Clamping at the receiver's length makes the claimed length false.
/** @requires s.length === 2 */
function pair(s: string): string { return s; }
export function clamped(s: string): string {
  const part = s.slice(0, 2);
  return pair(part);
}
