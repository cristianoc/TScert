// Bounds pattern P18, the supported neighbour of
// `bounds-pattern-two-field-guard-refused`: a guard of one field.
// Pretext: line-break.ts's guarded nullable lists.
/** @invariant this.extras === null || this.extras.length === this.widths.length */
export type Flat = { /** @stable */ readonly widths: number[]; /** @stable */ readonly extras: number[] | null };
type Cursor = { segment: number };

function step(c: Cursor): Modifies<{ values: "any" }, void> {
  c.segment++;
}

export function oneField(p: Flat, c: Cursor): number {
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i */
  for (let i = 0; i < p.widths.length; i++) {
    step(c);
    const extras = p.extras;
    if (extras !== null) s += extras[i]!;
  }
  return s;
}
