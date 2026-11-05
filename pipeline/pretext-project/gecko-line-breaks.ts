// A predicate exported as a constant arrow with no result annotation, as
// pretext's src/gecko-line-breaks.ts exports `isSpaceOrTabOrSegmentBreak`.
export const isSpaceOrTabOrSegmentBreak = (ch: number) =>
  ch === 0x20 || ch === 0x09 || ch === 0x0a;
