// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-break.ts#breaksAfterKind, line-break.ts#consumesAtLineStart,
// line-break.ts#countPreparedLines, line-break.ts#countSteppedLines,
// line-break.ts#getItemTabAdvance, line-break.ts#getTabAdvance,
// line-break.ts#getTerminalLetterSpacing,
// line-break.ts#isDiscretionaryLineEnd, line-break.ts#normalizeMaxWidth,
// line-break.ts#normalizePreparedLineStart,
// line-break.ts#returnsFromUnfitHyphen, line-break.ts#staysAfterObject,
// line-break.ts#stepPreparedLineGeometryFromStart,
// line-break.ts#stepPreparedSimpleLineGeometry,
// line-break.ts#walkPreparedComplexLines,
// line-break.ts#walkPreparedLinesRaw.
// Refusal: gate: missing type annotation in walkPreparedComplexLines.
// A parameter with a default and no annotation (`singleLine = false`): a
// unit's boundary is written, so the parameter needs its type. Pretext's
// `walkPreparedComplexLines` is refused, and read at its declared signature
// it refuses its module.
export function lines(width: number, singleLine = false): number {
  return singleLine ? 1 : width;
}
