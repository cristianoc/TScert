// A path precondition no caller's fact establishes: pretext's
// `layoutNextRichInlineLineRange` (src/rich-inline.ts) calls
// `getSegmentIndex(flow, start)`, `start` its exported parameter, of whose
// `itemIndex` nothing states a safe integer at least 0. Safe where callers
// pass cursors the module made; closing it needs an invariant of the cursor
// type or a validated entry (docs/drafts/field-paths-and-record-invariants.md,
// "Record invariants").
type Paragraph = { itemSegments: number[]; widths: number[] };
type Cursor = { itemIndex: number; segmentIndex: number };

/** @requires safeInteger(cursor.itemIndex) && 0 <= cursor.itemIndex */
function getSegmentIndex(flow: Paragraph, cursor: Cursor): number {
  const { itemSegments } = flow;
  return cursor.itemIndex < itemSegments.length
    ? itemSegments[cursor.itemIndex]! + cursor.segmentIndex
    : flow.widths.length;
}

export function lineStart(flow: Paragraph, start: Cursor): number {
  return getSegmentIndex(flow, start);
}
