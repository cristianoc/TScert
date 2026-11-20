// A write keeps what is known of another key of any object: after `c.i = j`,
// the write `h.extras = []` is under the key `extras`, so it finds a location
// other than `c.i`'s, whether or not `c` is `h`, and `c.i === j` holds at
// the return (the note *Tolerant frames*, (W3)).
type Cursor = { i: number };
export type H = { readonly widths: readonly number[]; extras: number[] | null };

/** @requires safeInteger(j)
 * @ensures safeInteger(c.i) && c.i === j */
export function moveTo(c: Cursor, h: H, j: number): void {
  c.i = j;
  h.extras = [];
}
