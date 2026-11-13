// Bounds pattern P18: a guarded fact through two fields.
// Fact: p.items === null || p.items.insideExtras === null ||
// p.items.insideExtras.length === p.widths.length at the loop head, both
// fields `@stable`.
// Pretext: line-break.ts stepPreparedSimpleLineGeometry (2 sites).
// Gap: a guard is eliminated and kept only where its path is a slot or one
// field; a guard of two fields is kept by no heap change.
type Items = { /** @stable */ readonly insideExtras: number[] | null };
/** @invariant this.items === null || this.items.insideExtras === null || this.items.insideExtras.length === this.widths.length */
export type Prepared = { /** @stable */ readonly widths: number[]; /** @stable */ readonly items: Items | null };
type Cursor = { segment: number };

function step(c: Cursor): Modifies<{ values: "any" }, void> {
  c.segment++;
}

export function acrossStep(p: Prepared, c: Cursor): number {
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i */
  for (let i = 0; i < p.widths.length; i++) {
    step(c);
    const items = p.items;
    if (items !== null) {
      const extras = items.insideExtras;
      if (extras !== null) s += extras[i]!;
    }
  }
  return s;
}

export function noCall(p: Prepared): number {
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i */
  for (let i = 0; i < p.widths.length; i++) {
    const items = p.items;
    if (items !== null) {
      const extras = items.insideExtras;
      if (extras !== null) s += extras[i]!;
    }
  }
  return s;
}
