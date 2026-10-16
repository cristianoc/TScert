// A fresh array literal at a parameter whose binders are bounded by literal
// types is built at the parameter read at those bounds, as TypeScript keeps
// the literal's literal types there: `[0, 1]` is a pair whose first position
// is `0 | 1`, and `K` is inferred from it.
declare function pick<K extends 0 | 1>(entries: Array<[K, number]>): K;

export function constraintSatisfied(): 0 | 1 {
  const k: 0 | 1 = pick([[0, 1]]);
  return k;
}
