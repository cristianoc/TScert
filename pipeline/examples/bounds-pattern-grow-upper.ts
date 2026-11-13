// Bounds pattern P4, the supported neighbours of
// `bounds-pattern-grow-upper-refused`: the bound taken once as a variable, a
// lower bound of a.starts.length that growth keeps (`lower`), and the
// regional frame over parameters in a loop (`slots`, `listSlots`).
// Pretext: prepare.ts measureAnalysis's reads below `count`.
export type Analysis = {
  /** @stable */ readonly starts: number[];
  /** @stable */ readonly flags: number[];
};
type Lists = { /** @stable */ readonly widths: number[] };

function note(out: number[], v: number): Modifies<{ values: "any"; stores: "grow" }, void> {
  out.push(v);
}

function noteIn(out: number[], v: number): Modifies<{ values: "any"; stores: "keep"; "out[*]": "any" }, void> {
  out.push(v);
}

function measure(n: number, p: Lists | null): Modifies<{ values: "any"; stores: "keep"; "p.widths[*]": "any" }, number> {
  if (p !== null) p.widths.push(n);
  return n;
}

/** @requires a.flags.length === a.starts.length */
export function lower(a: Analysis, out: number[]): number {
  const n = a.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && n <= a.starts.length */
  for (let i = 0; i + 1 < n; i++) {
    note(out, i);
    s += a.starts[i + 1]!;
  }
  return s;
}

/** @requires flags.length === starts.length && flags !== out && starts !== out */
export function slots(flags: number[], starts: number[], out: number[]): number {
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && flags.length <= starts.length && flags !== out && starts !== out */
  for (let i = 0; i + 1 < flags.length; i++) {
    noteIn(out, i);
    s += starts[i + 1]!;
  }
  return s;
}

/** @requires flags.length === starts.length */
export function listSlots(flags: number[], starts: number[]): number {
  const widths: number[] = [];
  const lists: Lists = { widths };
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && flags.length === starts.length && flags !== lists.widths && starts !== lists.widths */
  for (let i = 0; i < flags.length; i++) {
    measure(i, lists);
    s += starts[i]!;
  }
  return s;
}
