// Bounds pattern P1: a visitor of unknown effect between reads.
// Fact: 0 <= i < xs.length kept across a call of `walk`, whose effect is its
// visitor parameter's; with no visitor passed the call changes nothing.
// Pretext: line-break.ts walkPreparedLinesRaw, countSteppedLines,
// walkPreparedComplexLines (48 sites); rich-inline.ts prepareRichInline (2).
// Gap: a function-typed parameter whose type states no effect gives the
// walker the effect any, at every call, `undefined` passed included, so no
// bound on a length survives the call; `widthsWalk`, the walker's own loop
// over a `number[]`, loses its bound at each visit the same way.
type Visitor = (w: number) => void;

function walk(xs: number[], visit: Visitor | undefined): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s += xs[i]!;
    if (visit !== undefined) visit(s);
  }
  return s;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function afterWalk(xs: number[], i: number): number {
  const w = walk(xs, undefined);
  return w + xs[i]!;
}

export type Prepared = { widths: number[]; flags: Uint8Array };

/** @requires prepared.flags.length === prepared.widths.length */
export function widthsWalk(prepared: Prepared, visit: Visitor): number {
  const { widths } = prepared;
  const count = widths.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(count) && count <= widths.length */
  for (let i = 0; i < count; i++) {
    visit(i);
    s += widths[i]!;
  }
  return s;
}
