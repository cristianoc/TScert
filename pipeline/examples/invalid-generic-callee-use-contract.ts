// The contract the call `reverse(result)` fixes is a list of numbers; the
// last write is a cell holding a string when `n > 2`: `count(3)` returns a
// list whose head is "many". The write is refused at the contract.
type List<T> = null | { head: T; tail: List<T> };

function reverse<T>(l: List<T>): List<T> {
  let result: List<T> = null;
  while (l !== null) {
    result = { head: l.head, tail: result };
    l = l.tail;
  }
  return result;
}

export function count(n: number): List<number> {
  let result = null;
  for (let i = 0; i < n; i++) {
    result = { head: i, tail: result };
  }
  result = n > 2 ? { head: "many", tail: null } : result;
  return reverse(result);
}
