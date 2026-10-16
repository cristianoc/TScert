// An iterator whose type states no `return`: leaving the loop early, or a
// throw out of its body, calls the iterator's `return` if it owns one, and
// its open record type says nothing of what that property holds.
interface Numbers {
  [Symbol.iterator](): { next(): { readonly value: number; done: boolean } };
}

export function total(values: Numbers): number {
  let sum = 0;
  for (const n of values) sum = sum + n;
  return sum;
}
