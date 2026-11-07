// Reads bounded by the length of an array a record's field holds: pretext's
// `getTerminalLetterSpacing` (src/line-break.ts) reads `segmentFlags[i]!`,
// `segmentFlags` a field of its `PreparedLineBreakData` parameter, and
// `getSegmentIndex` (src/rich-inline.ts) reads `itemSegments[cursor.itemIndex]!`,
// the index a field of its cursor. A written precondition names the field's
// element count or the cursor's index as a path, `prepared.segmentFlags.length`
// or `cursor.itemIndex`; the read through the path, or through a binding the
// field is destructured into, is below the length; callers establish each
// precondition by a test of the path, in a loop through calls keeping the
// heap, through a binding of a nested path's length, or by their own.

type Prepared = { widths: number[]; segmentFlags: Uint8Array };

/** @requires safeInteger(segmentIndex) && 0 <= segmentIndex && segmentIndex < prepared.segmentFlags.length */
function flagAt(prepared: Prepared, segmentIndex: number): number {
  return prepared.segmentFlags[segmentIndex]!;
}

/** @requires safeInteger(segmentIndex) && 0 <= segmentIndex && segmentIndex < prepared.segmentFlags.length */
function destructuredFlag(prepared: Prepared, segmentIndex: number): number {
  const { segmentFlags } = prepared;
  return segmentFlags[segmentIndex]!;
}

/** @requires safeInteger(i) && 0 <= i && i < prepared.widths.length */
function widthAt(prepared: Prepared, i: number): number {
  return prepared.widths[i]!;
}

// The callers establish each precondition by a loop's test of the path.
export function sumFlags(prepared: Prepared): number {
  let s = 0;
  for (let i = 0; i < prepared.segmentFlags.length; i++)
    s = s + flagAt(prepared, i) + destructuredFlag(prepared, i);
  return s;
}

export function sumWidths(prepared: Prepared): number {
  let s = 0;
  for (let i = 0; i < prepared.widths.length; i++) s = s + widthAt(prepared, i);
  return s;
}

// A nested path: a field of a field.
type Paragraph = { data: Prepared; itemSegments: number[] };

/** @requires safeInteger(i) && 0 <= i && i < flow.data.widths.length */
function nestedWidth(flow: Paragraph, i: number): number {
  return flow.data.widths[i]!;
}

export function lastWidth(flow: Paragraph): number {
  const n = flow.data.widths.length;
  if (n > 0) return nestedWidth(flow, n - 1);
  return 0;
}

// pretext's `getSegmentIndex` (src/rich-inline.ts): an index a record holds,
// bounded by the test before the read, its integrality written as a clause.
type Cursor = { itemIndex: number; segmentIndex: number };

/** @requires safeInteger(cursor.itemIndex) && 0 <= cursor.itemIndex */
function getSegmentIndex(flow: Paragraph, cursor: Cursor): number {
  const { itemSegments } = flow;
  return cursor.itemIndex < itemSegments.length
    ? itemSegments[cursor.itemIndex]! + cursor.segmentIndex
    : flow.data.widths.length;
}

/** @requires safeInteger(cursor.itemIndex) && 0 <= cursor.itemIndex */
function nextSegment(flow: Paragraph, cursor: Cursor): number {
  return getSegmentIndex(flow, cursor) + 1;
}
