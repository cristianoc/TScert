// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-breaks.ts#getWordSegmenter.
// `new Intl.Segmenter(…)`, through the namespace's reviewed construct
// entry, and a loop over its `segment(text)`.
export function words(text: string): number {
  const segmenter = new Intl.Segmenter(undefined, { granularity: "word" });
  let n = 0;
  for (const _ of segmenter.segment(text)) n++;
  return n;
}
