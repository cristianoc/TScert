// A guard finding an object where an assigned parameter held in a cell (a
// closure created before its writes mentions it) holds one beside `null`:
// what a cell is known to hold is primitive values, or its contract less
// `undefined`, so the read through it is refused by that reason.
type List = null | { head: number; tail: List };
export function length(l: List): number {
  const peek = (): List => l;
  let n = 0;
  while (l !== null) {
    n = n + 1;
    l = l.tail;
  }
  return n + (peek() === null ? 0 : 1);
}
