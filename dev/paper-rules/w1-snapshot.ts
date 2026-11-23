// W1 as Pretext writes it, with the local copy of the handle's field
// (`const { segmentFlags } = prepared`), changed to read through the handle:
// the pass drops the link from a local to the field it was read from at a
// loop head (docs/drafts/loop-head-links.md). REVERT once that is fixed: the
// two reads marked below go back to the local `widths`.
type AtMost<P> = unknown;
type LineVisitor<E> = (width: number, start: number, end: number) => void;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };
type Flow = { data: Prepared; wholeWidth: number; widths: number[] };

export function walkLines<E extends AtMost<'{ "prepared.**": "keep", "else": "any" }'>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {   // REVERT: widths.length
    const start = cursor.segmentIndex;
    onLine(prepared.widths[start]!, start, start + 1);   // REVERT: widths[start]
    // After the visit: the cursor, the handle's field and its array are
    // read again, relying on the facts the visit kept.
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;   // REVERT: widths[…]
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

