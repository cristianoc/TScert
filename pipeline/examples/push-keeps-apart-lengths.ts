// pretext analysis.ts: segmentAtLineBreaks slices each segment's text once,
// after its loop has pushed the segments' flags. A push grows only its
// receiver's store, so `texts.push(…)` keeps the length of `flags`, an array
// allocated apart from `texts` (PROGRAM-TYPING.md, "Linear facts", the
// append relation), and the two stay apart across a push of an actual that
// writes no heap: the loop keeps `count === flags.length` and gains
// `texts.length === j`.

export type Analysis = { texts: string[]; flags: number[] };

/** @ensures result.texts.length === result.flags.length */
export function segment(normalized: string): Analysis {
  const flags: number[] = [];
  for (let i = 0; i < normalized.length; i++)
    flags.push(normalized.charCodeAt(i) & 15);
  const count = flags.length;
  const texts: string[] = [];
  /** @invariant safeInteger(j) && safeInteger(count) && 0 <= j && j <= count && texts.length === j && count === flags.length */
  for (let j = 0; j < count; j++) texts.push(normalized.slice(j, j + 1));
  return { texts, flags };
}

export function lastText(normalized: string): string {
  const analysis = segment(normalized);
  const n = analysis.flags.length;
  return n === 0 ? "" : analysis.texts[n - 1]!;
}
