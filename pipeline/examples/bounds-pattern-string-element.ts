// Bounds pattern P11, the supported neighbour of
// `bounds-pattern-string-element-refused`: a code unit read below the length.
// Pretext: analysis.ts segmentAtLineBreaks.
export function goodCode(text: string): number {
  let s = 0;
  for (let i = 0; i < text.length; i++) s += text.charCodeAt(i);
  return s;
}
