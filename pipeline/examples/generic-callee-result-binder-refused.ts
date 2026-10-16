// A generic callee whose binder occurs in its result, at an expected type
// that says nothing of it: relating `{ head: T }` to `{}` gives `T` no bound,
// so the argument is no use at one type, and the evolving binding's
// contract does not settle.

function first<T>(l: { head: T }): { head: T } {
  return { head: l.head };
}

export function count(k: number): {} {
  let result = null;
  for (let i = 0; i < k; i++) {
    result = { head: i, tail: result };
  }
  return first(result);
}
