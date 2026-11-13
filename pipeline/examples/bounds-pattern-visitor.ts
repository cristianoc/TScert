// Bounds pattern P1, the supported neighbours of `bounds-pattern-visitor-refused`:
// a visitor whose type states its effect (`Modifies<{ values: "any"; stores:
// "grow" }, void>`), a walker with no visitor, and a typed array's length,
// which no visitor changes, read below a count taken at entry.
// Pretext: line-break.ts walkPreparedComplexLines and its callers.
type Visitor = (w: number) => void;
type BoundedVisitor = (w: number) => Modifies<{ values: "any"; stores: "grow" }, void>;

function walkBounded(xs: number[], visit: BoundedVisitor | undefined): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s += xs[i]!;
    if (visit !== undefined) visit(s);
  }
  return s;
}

function walkPlain(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) s += xs[i]!;
  return s;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function afterBounded(xs: number[], i: number): number {
  const w = walkBounded(xs, undefined);
  return w + xs[i]!;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function afterPlain(xs: number[], i: number): number {
  const w = walkPlain(xs);
  return w + xs[i]!;
}

export type Prepared = { widths: number[]; flags: Uint8Array };

/** @requires prepared.flags.length === prepared.widths.length */
export function flagsWalk(prepared: Prepared, visit: Visitor): number {
  const { widths, flags } = prepared;
  const count = widths.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(count) && count === flags.length */
  for (let i = 0; i < count; i++) {
    visit(i);
    s += flags[i]!;
  }
  return s;
}
