// Bounds pattern P10: equal counts computed by two functions of one input.
// Fact: e.length = w.length, both the count of non-space units of `text`.
// Pretext: prepare.ts measureAnalysis (6 sites: fitAdvances against
// extraSpacings and unspaced graphemes); rich-inline.ts prepareRichInline (1).
// Gap: neither builder's result length is a linear term of `text`, and no
// clause names a count both functions compute.
function ends(text: string): number[] {
  const out: number[] = [];
  for (let i = 0; i < text.length; i++) if (text.charCodeAt(i) !== 32) out.push(i);
  return out;
}

function widthsOf(text: string): number[] {
  const out: number[] = [];
  for (let i = 0; i < text.length; i++) if (text.charCodeAt(i) !== 32) out.push(1);
  return out;
}

export function paired(text: string): number {
  const e = ends(text);
  const w = widthsOf(text);
  let s = 0;
  for (let k = 0; k < e.length; k++) s += w[k]!;
  return s;
}
