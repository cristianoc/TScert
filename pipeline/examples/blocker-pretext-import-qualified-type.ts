// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// gecko-line-breaks.ts#getGeckoLineBreaks,
// gecko-line-breaks.ts#getLineBreakClass,
// gecko-line-breaks.ts#isClusterExtender,
// gecko-line-breaks.ts#isClusterExtenderExcludingJoiners,
// gecko-line-breaks.ts#isEastAsianPunctuation,
// gecko-line-breaks.ts#isEastAsianSegmentBreak,
// gecko-line-breaks.ts#isEastAsianWidthFHWExcludingEmoji,
// gecko-line-breaks.ts#isJapaneseOrChinese,
// gecko-line-breaks.ts#isSegmentBreakSkipChar,
// gecko-line-breaks.ts#segmentComplex, line-breaks.ts#classify,
// line-breaks.ts#clearWordSegmenter, line-breaks.ts#createFactory,
// line-breaks.ts#following, line-breaks.ts#getBlinkDefaultLocale,
// line-breaks.ts#getBlinkLineBreaks, line-breaks.ts#getBreakLanguage,
// line-breaks.ts#getBreakRules, line-breaks.ts#getClass,
// line-breaks.ts#getWebKitBreakBetweenItems,
// line-breaks.ts#getWebKitLineBreaks, line-breaks.ts#getWebKitLineRules,
// line-breaks.ts#isASCIIAlpha, line-breaks.ts#isASCIIDigit,
// line-breaks.ts#isBlinkBreakableSpace, line-breaks.ts#isComplexContext,
// line-breaks.ts#isWebKitBreakableSpace, line-breaks.ts#lazyRegExp,
// line-breaks.ts#markDictionaryWords, line-breaks.ts#markRuleBoundaries,
// line-breaks.ts#nextBreakablePosition, line-breaks.ts#nextBreakableSpace,
// line-breaks.ts#shouldBreakFast, line-breaks.ts#shouldKeepAfterKeepAll,
// line-breaks.ts#unpackClasses, line-breaks.ts#unpackStateRows,
// line-breaks.ts#unpackTableRows.
// Refusal: gate: a qualified type reference in getWordSegmenter.
// An imported function whose result is `Intl.Segmenter`, a qualified type
// reference, read at its declared signature. Pretext's `getWordSegmenter`
// meets it in its own module and in each module importing it.
import { getWordSegmenter } from "../pretext-project/line-breaks.ts";

export function wordStarts(text: string): number[] {
  const starts: number[] = [];
  for (const part of getWordSegmenter().segment(text)) starts.push(part.index);
  return starts;
}
