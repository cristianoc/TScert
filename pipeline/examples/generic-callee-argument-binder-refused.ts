// A generic callee whose binder occurs only in its parameter: the call's
// expected type, `number`, says nothing of `T`, so the argument is no use
// at one type, and the evolving binding's contract does not settle.
type List<T> = null | { head: T; tail: List<T> };

function size<T>(l: List<T>): number {
  let n = 0;
  while (l !== null) {
    n = n + 1;
    l = l.tail;
  }
  return n;
}

export function count(k: number): number {
  let result = null;
  for (let i = 0; i < k; i++) {
    result = { head: i, tail: result };
  }
  return size(result);
}
