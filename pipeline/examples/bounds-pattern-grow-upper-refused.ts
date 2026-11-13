// Bounds pattern P4: an upper bound of a length across a call growing stores.
// Fact: a.flags.length <= a.starts.length across a callee whose frame names
// its region (`"out[*]": "any"`), with both arrays stated apart from `out`,
// so the test i + 1 < a.flags.length bounds the read of a.starts.
// Pretext: prepare.ts measureAnalysis, addKanaKerning,
// addIdeographicSpaceHangs; han-kerning.ts getHanKerningTrims;
// measurement.ts getSegmentFit, countLigaturesOnFirstLetter,
// measureFitAdvances; rich-inline.ts prepareRichInline (18 sites).
// Gap: a length read through a `@stable` path is not kept across a regional
// store frame (`regional`, `paths`), and a slot's length is not kept across
// one outside a loop (`straight`), although the arrays are apart from it.
export type Analysis = {
  /** @stable */ readonly starts: number[];
  /** @stable */ readonly flags: number[];
};
type Lists = { /** @stable */ readonly widths: number[] };

function noteAt(out: number[], v: number): Modifies<{ values: "any"; "out[*]": "any" }, void> {
  out.push(v);
}

function noteIn(out: number[], v: number): Modifies<{ values: "any"; stores: "keep"; "out[*]": "any" }, void> {
  out.push(v);
}

function measure(n: number, p: Lists | null): Modifies<{ values: "any"; stores: "keep"; "p.widths[*]": "any" }, number> {
  if (p !== null) p.widths.push(n);
  return n;
}

/** @requires a.flags.length === a.starts.length && a.flags !== out && a.starts !== out */
export function regional(a: Analysis, out: number[]): number {
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && a.flags.length <= a.starts.length && a.flags !== out && a.starts !== out */
  for (let i = 0; i + 1 < a.flags.length; i++) {
    noteAt(out, i);
    s += a.starts[i + 1]!;
  }
  return s;
}

/** @requires a.flags.length === a.starts.length */
export function paths(a: Analysis): number {
  const widths: number[] = [];
  const lists: Lists = { widths };
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && a.flags.length === a.starts.length && a.flags !== lists.widths && a.starts !== lists.widths */
  for (let i = 0; i < a.flags.length; i++) {
    measure(i, lists);
    s += a.starts[i]!;
  }
  return s;
}

/** @requires flags.length === starts.length && flags !== out && starts !== out && safeInteger(i) && 0 <= i */
export function straight(flags: number[], starts: number[], out: number[], i: number): number {
  if (i + 1 < flags.length) {
    noteIn(out, i);
    return starts[i + 1]!;
  }
  return 0;
}
