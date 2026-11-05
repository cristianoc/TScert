// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// after its rewrites of element reads elsewhere): line-break.ts#isDiscretionaryLineEnd,
// line-break.ts#getItemTabAdvance, line-break.ts#getTerminalLetterSpacing,
// line-break.ts#normalizePreparedLineStart, line-break.ts#walkPreparedLinesRaw,
// line-break.ts#countSteppedLines, line-break.ts#staysAfterObject,
// line-break.ts#returnsFromUnfitHyphen; with countPreparedLines and
// stepPreparedSimpleLineGeometry, whose first refusals are
// blocker-pretext-parallel-element-cast and
// blocker-pretext-argument-implied-assertion.
// Refusal: reject: source expression obligation: no derivation of its cast
// claim.
// A non-null assertion of an element read at an index bounded by another
// array's length, `flags[i]!` with `i < widths.length`: nothing relates the
// two lengths, so the read past `flags`' end is `undefined`, returned as a
// number (run under Node). Pretext's walkers read `segmentFlags` and the
// other per-segment arrays inside `widths.length`, a count parameter, or an
// index no test bounds; the read that verifies checks the element,
// `defined(flags[i])`.
type Prepared = { widths: number[]; flags: Uint8Array };

export function lastFlag(prepared: Prepared): number {
  const { widths, flags } = prepared;
  let last = 0;
  for (let i = 0; i < widths.length; i++) last = flags[i]!;
  return last;
}
