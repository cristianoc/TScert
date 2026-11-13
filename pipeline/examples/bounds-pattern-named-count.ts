// Bounds pattern P10, the supported neighbour of
// `bounds-pattern-named-count-refused`: one builder's result read below its
// own length.
// Pretext: prepare.ts measureAnalysis's grapheme lists.
function widthsOf(text: string): number[] {
  const out: number[] = [];
  for (let i = 0; i < text.length; i++) if (text.charCodeAt(i) !== 32) out.push(1);
  return out;
}

export function single(text: string): number {
  const w = widthsOf(text);
  let s = 0;
  for (let k = 0; k < w.length; k++) s += w[k]!;
  return s;
}
