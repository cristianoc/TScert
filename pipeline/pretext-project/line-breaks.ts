// A function whose result is a qualified type reference, as pretext's
// src/line-breaks.ts exports `getWordSegmenter`.
export function getWordSegmenter(): Intl.Segmenter {
  return new Intl.Segmenter(undefined, { granularity: "word" });
}
