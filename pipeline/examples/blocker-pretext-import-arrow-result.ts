// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): analysis.ts#analyzeText,
// analysis.ts#removeSkippableSegmentBreaks,
// analysis.ts#segmentAtLineBreaks.
// Refusal: gate: a declared value must be an annotated constant, function
// or class: isSpaceOrTabOrSegmentBreak.
// An imported constant holding an arrow whose parameters are annotated and
// whose result is not: the declaration states no result type, so its use is
// refused. TypeScript's `isolatedDeclarations` refuses the declaration too
// (TS9007): a function's result needs an annotation there. The source
// states `: boolean`.
import { isSpaceOrTabOrSegmentBreak } from "../pretext-project/gecko-line-breaks.ts";

export function countSpaces(text: string): number {
  let count = 0;
  for (let i = 0; i < text.length; i++)
    if (isSpaceOrTabOrSegmentBreak(text.charCodeAt(i))) count++;
  return count;
}
