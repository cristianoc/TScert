// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// analysis.ts#classifySegmentBreakCode, analysis.ts#classifySegmentUnit,
// analysis.ts#collapseWhitespaceNormal, analysis.ts#followsChunkContent,
// analysis.ts#gathersKind, analysis.ts#getTrailingCollapsibleStart,
// analysis.ts#isCollapsibleSpaceCode, analysis.ts#isControlSegmentCode,
// analysis.ts#isSegmentBreakRunSpace, analysis.ts#markItemStarts,
// analysis.ts#normalizeWhitespacePreWrap,
// analysis.ts#removeItemsSkippableSegmentBreaks,
// gecko-line-breaks.ts#extendCluster,
// gecko-line-breaks.ts#getComplexLanguage,
// gecko-line-breaks.ts#hasCompressedLeadingWhitespace,
// gecko-line-breaks.ts#isDiscardable, gecko-line-breaks.ts#isInvalidChar,
// gecko-line-breaks.ts#isKeepAllLetter,
// gecko-line-breaks.ts#isSpaceCombiningSequenceTail,
// gecko-line-breaks.ts#isTrimmableSpace,
// gecko-line-breaks.ts#markWordBreaks, gecko-line-breaks.ts#readCodePoint,
// gecko-line-breaks.ts#setupClusterBoundaries,
// gecko-line-breaks.ts#splitAndInitTextRun, graphemes.ts#findGraphemeEnds,
// graphemes.ts#isBidiControl, han-kerning.ts#getCharType,
// han-kerning.ts#getFontData, han-kerning.ts#getHanKerningTrims,
// han-kerning.ts#getStaticCharType, han-kerning.ts#getTrim,
// han-kerning.ts#getTypeFromBounds, han-kerning.ts#haltedSide,
// han-kerning.ts#isCanvasCjkSymbol, han-kerning.ts#maybeHanKerns,
// han-kerning.ts#textMayHanKern, prepare.ts#addInternalLetterSpacing,
// prepare.ts#countRenderedSpacingGraphemes,
// prepare.ts#getFollowingSpaceTail, prepare.ts#getScriptFacts,
// prepare.ts#getScriptFactsAt, prepare.ts#isSpaceKind,
// prepare.ts#mayHoldCursive, prepare.ts#needsComplexTextPath,
// prepare.ts#readScriptRuns, prepare.ts#spaceSharesScriptRun.
// A record type with a `Uint16Array` field, read through the overlay of
// library types: a view of bytes, whose declarations are not read. Pretext
// meets it in its own type `TextAnalysis` and in the modules importing it.
export type Analysis = { sources: Uint16Array | null; texts: string[] };
export function count(a: Analysis): number {
  return a.texts.length;
}
