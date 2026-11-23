// W1 with Pretext's local copy of the handle's field
// (`const { segmentFlags } = prepared`): the walker guards and reads the
// local `widths`. Safe under the bound, which keeps the handle's reach. The
// pass drops the link from `widths` to `prepared.widths` at the loop head
// (cristianoc/TScert#351), so the walker states it with the prototype's
// unsafe assume, which names the issue in its verdict.
type AtMost<P> = unknown;
type LineVisitor<E> = (width: number, start: number, end: number) => void;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };
type Flow = { data: Prepared; wholeWidth: number; widths: number[] };

function paperAssume(fact: boolean, issue: string): Modifies<{}, void> {}

export function walkLines<E extends AtMost<'{ "prepared.**": "keep", "else": "any" }'>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  const widths = prepared.widths;
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < widths.length) {
    paperAssume(widths === prepared.widths, "#351"); // unsafe assume until #351: the pass drops the link at the loop head
    const start = cursor.segmentIndex;
    onLine(widths[start]!, start, start + 1);
    // After the visit: the cursor, the handle's field and its array are
    // read again, relying on the facts the visit kept.
    lines += widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}
