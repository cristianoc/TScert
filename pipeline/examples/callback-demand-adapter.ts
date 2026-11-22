// Support-parametric callback demand through an adapting closure wrapper
// (`walkLines`, modeling Pretext's `walkRichInlineLineRanges`): `walkLines`
// wraps `visit` in `(w, f) => visit({ width: w, flag: f })`, forwarding
// `walkRaw`'s path demand onto `visit`. `collectAdapted` discharges the
// forwarded demand via freshly allocated `walked`.
export interface PreparedData {
  widths: number[];
  segmentFlags: number[];
}

export interface Line {
  width: number;
  flag: number;
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
function walkLines(prepared: PreparedData, visit: (line: Line) => void): void {
  walkRaw(prepared, (w, f) => {
    visit({ width: w, flag: f });
  });
}

/** @requires prepared.widths.length === prepared.segmentFlags.length */
export function collectAdapted(prepared: PreparedData): number[] {
  const walked: number[] = [];
  walkLines(prepared, (line) => {
    walked.push(line.width);
  });
  return walked;
}
