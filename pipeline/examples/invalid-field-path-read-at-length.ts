// A call outside a path's precondition: `flagAt(prepared, n)` with `n` the
// flags' element count reads past their end, `undefined` at `number` (run
// under Node: `atEnd({ widths: [1], segmentFlags: new Uint8Array(1) })` is
// `undefined`).
type Prepared = { widths: number[]; segmentFlags: Uint8Array };

/** @requires safeInteger(segmentIndex) && 0 <= segmentIndex && segmentIndex < prepared.segmentFlags.length */
function flagAt(prepared: Prepared, segmentIndex: number): number {
  return prepared.segmentFlags[segmentIndex]!;
}

export function atEnd(prepared: Prepared): number {
  return flagAt(prepared, prepared.segmentFlags.length);
}
