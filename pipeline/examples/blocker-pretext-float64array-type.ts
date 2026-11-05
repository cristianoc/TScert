// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// han-kerning.ts#getCharType, han-kerning.ts#getFontData,
// han-kerning.ts#getHanKerningTrims, han-kerning.ts#getStaticCharType,
// han-kerning.ts#getTrim, han-kerning.ts#getTypeFromBounds,
// han-kerning.ts#haltedSide, han-kerning.ts#isCanvasCjkSymbol,
// han-kerning.ts#maybeHanKerns, han-kerning.ts#textMayHanKern,
// prepare.ts#addInternalLetterSpacing,
// prepare.ts#countRenderedSpacingGraphemes,
// prepare.ts#getFollowingSpaceTail, prepare.ts#getScriptFacts,
// prepare.ts#getScriptFactsAt, prepare.ts#getUnspacedGraphemes,
// prepare.ts#isSpaceKind, prepare.ts#mayHoldCursive,
// prepare.ts#needsComplexTextPath, prepare.ts#readScriptRuns,
// prepare.ts#spaceSharesScriptRun.
// A record type with a `Float64Array` field, read through the overlay of
// library types: a view whose elements are doubles, whose declarations are
// not read. Pretext meets it in its measurement record and in the modules
// importing it.
export type Measurement = { kanaKerning: Float64Array | null; size: number };
export function size(m: Measurement): number {
  return m.size;
}
