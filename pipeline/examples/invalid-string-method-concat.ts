// Numeric conversion does not contribute one UTF-16 unit in general.
/** @requires s.length === 1 */
function one(s: string): string { return s; }
export function numeric(n: number): string {
  const s = "" + n;
  return one(s);
}
