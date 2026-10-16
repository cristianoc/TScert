// An unannotated `let` of `null` consed onto itself: its written types never
// settle, and its contract is the type its return expects, against which
// each write is checked.
type List<T> = null | { head: T; tail: List<T> };

export function reverse<T>(l: List<T>): List<T> {
  let result = null;
  while (l !== null) {
    result = { head: l.head, tail: result };
    l = l.tail;
  }
  return result;
}
