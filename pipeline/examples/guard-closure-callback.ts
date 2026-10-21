// A guard closure passed where a callback binding more parameters is
// expected (`every`'s and `filter`'s predicate takes the element, its index
// and the array) is offered that signature beside its own and its promise:
// its body is checked at each, the promise over its own parameter. The
// reviewed `every` states no guard overload and narrows nothing; `filter` is
// called at its guard overload, whose result, promising `string`, is read
// where `(string | null)[]` is expected.
export function allPresent(xs: (string | null)[]): boolean {
  return xs.every((x): x is string => x !== null);
}
export function present(xs: (string | null)[]): (string | null)[] {
  return xs.filter((x): x is string => x !== null);
}
