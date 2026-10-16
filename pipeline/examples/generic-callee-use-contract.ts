// An evolving `let` whose only typed use is the argument of a generic
// callee: the call's expected type, the result, fixes the callee's binder,
// and the parameter at that instance is the binding's contract.
type List<T> = null | { head: T; tail: List<T> };

function reverse<T>(l: List<T>): List<T> {
  let result: List<T> = null;
  while (l !== null) {
    result = { head: l.head, tail: result };
    l = l.tail;
  }
  return result;
}

export function fromArray<T>(...elts: T[]): List<T> {
  let result = null;
  for (let i = 0; i < elts.length; i++) {
    const elt = elts[i];
    if (elt !== undefined) {
      result = { head: elt, tail: result };
    }
  }
  return reverse(result);
}
