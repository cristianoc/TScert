// The standard library's `Intl.Segmenter` as pretext uses it
// (chenglou/pretext at 0d102a5c, src/line-breaks.ts and
// src/gecko-line-breaks.ts): a module binding holding a segmenter or
// `null`, made once by `??=` with `new Intl.Segmenter(undefined, {
// granularity: "word" })`, and loops over `segment(text)` reading each
// segment's `index`; besides, a segmenter of a named locale, a segment's
// `segment` and `isWordLike`, and a loop left early.
let wordSegmenter: Intl.Segmenter | null = null;

export function getWordSegmenter(): Intl.Segmenter {
  return (wordSegmenter ??= new Intl.Segmenter(undefined, {
    granularity: "word",
  }));
}

export function clearWordSegmenter(): void {
  wordSegmenter = null;
}

export function wordStarts(text: string, offset: number): number[] {
  const result: number[] = [];
  for (const part of getWordSegmenter().segment(text))
    if (part.index > 0) result.push(offset + part.index);
  return result;
}

export function firstWord(text: string): string {
  const segmenter = new Intl.Segmenter("th", {
    localeMatcher: "lookup",
    granularity: "word",
  });
  for (const segment of segmenter.segment(text)) {
    if (segment.isWordLike === true) return segment.segment;
  }
  return "";
}

export function graphemes(text: string): number {
  let n = 0;
  for (const segment of new Intl.Segmenter(undefined, undefined).segment(text))
    n += segment.input.length > 0 ? 1 : 0;
  return n;
}
