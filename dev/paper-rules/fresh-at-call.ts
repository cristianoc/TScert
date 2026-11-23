// An instance's root allocated by the caller, used after the call (rule
// Inst under the knowledge at the call; rule Alloc of Tolerant frames). The
// walker is w1.ts's, whose bound keeps the handle's declared reach. A use
// of the root that can only run after the call leaves it apart from the
// reach at the call; one that can run before the call may place it in the
// reach. Negative callers say whether the program is unsafe or only
// unprovable.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type LineVisitor<E extends Footprint> = (width: number, start: number, end: number) => Modifies<E, void>;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };
type Holder = { v: number[] };

export function walkLines<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(prepared.widths[start]!, start, start + 1);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

// Positive: the fresh list is returned after the call.
export function returnedAfter(p: Prepared): number[] {
  const widths: number[] = [];
  walkLines<{ "widths[*]": "extend" }>(p, (w) => { widths.push(w); });
  return widths;
}

// Positive: the fresh list is stored into a parameter's object after the
// call.
export function storedAfter(p: Prepared, out: Holder): number {
  const visited: number[] = [];
  const n = walkLines<{ "visited[*]": "extend" }>(p, (w) => { visited.push(w); });
  out.v = visited;
  return n;
}

// Negative, only unprovable: the list is stored before the call as the
// walked array itself, so the visitor grows the array the walker reads;
// every read stays in bounds (the loop runs until push throws at the
// maximal length).
export function storedBefore(p: Prepared): number {
  const visited: number[] = [1];
  p.widths = visited;
  return walkLines<{ "visited[*]": "extend" }>(p, (w) => { visited.push(w); });
}

// Negative, only unprovable: the store follows the call in the loop's body,
// so from the second iteration on the walked array is the list the visitor
// grows; as in storedBefore, every read stays in bounds.
export function storedInLoop(p: Prepared): number {
  const visited: number[] = [1];
  let n = 0;
  for (let k = 0; k < 2; k++) {
    n += walkLines<{ "visited[*]": "extend" }>(p, (w) => { visited.push(w); });
    p.widths = visited;
  }
  return n;
}

// Negative, only unprovable: the store is in a function declared after the
// call and run before it, so the walked array is the list the visitor grows,
// as in storedBefore.
export function storedByHoisted(p: Prepared): number {
  const visited: number[] = [1];
  stash();
  return walkLines<{ "visited[*]": "extend" }>(p, (w) => { visited.push(w); });
  function stash(): void { p.widths = visited; }
}
