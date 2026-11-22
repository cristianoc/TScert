// Support-parametric callback demand on nested record paths (`collectDirect`):
// `walkRaw` preserves `prepared.widths.length === prepared.segmentFlags.length`
// across `onEntry` and publishes a path-level demand on `prepared.widths` and
// `prepared.segmentFlags`. `collectDirect` mutates freshly allocated `walked`,
// separated from all pre-existing paths of `prepared` by path provenance.
export interface PreparedData {
  widths: number[];
  segmentFlags: number[];
}

type Cursor = { i: number };

/** @requires prepared.widths.length === prepared.segmentFlags.length */
function walkRaw(
  prepared: PreparedData,
  onEntry: (width: number, flag: number) => void,
): void {
  const c: Cursor = { i: 0 };
  /** @invariant safeInteger(c.i) && 0 <= c.i && prepared.widths.length === prepared.segmentFlags.length */
  while (c.i < prepared.widths.length) {
    const w = prepared.widths[c.i]!;
    const f = prepared.segmentFlags[c.i]!;
    onEntry(w, f);
    c.i++;
  }
}

/** @requires prepared.widths.length === prepared.segmentFlags.length */
export function collectDirect(prepared: PreparedData): number[] {
  const walked: number[] = [];
  walkRaw(prepared, (w, _f) => {
    walked.push(w);
  });
  return walked;
}
