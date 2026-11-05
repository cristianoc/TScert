// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-breaks.ts#getWordSegmenter.
// Refusal: gate: the global namespace Intl is read only by calling its
// functions, without spreads.
// `new Intl.Segmenter(…)`: the namespace `Intl` is admitted only for calls
// to its functions.
export function words(text: string): number {
  const segmenter = new Intl.Segmenter(undefined, { granularity: "word" });
  let n = 0;
  for (const _ of segmenter.segment(text)) n++;
  return n;
}
