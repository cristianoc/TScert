// A `let` pattern whose bindings are written: the pattern binds hidden
// names, then each source name is a cell of its own initialized with its
// value, its contract its initial value's type widened, as an unannotated
// `let`'s is.
export function swap(pair: [number, string]): string {
  let [n, s] = pair;
  n = n + 1;
  s = s + n;
  return s;
}

export function defaults(o: { a?: number; b: string }): number {
  let { a = 0, b } = o;
  if (b.length > 2) a = a * 2;
  b = "x";
  return a + b.length;
}

export function captured(o: { count: number }): () => number {
  let { count } = o;
  const bump = () => {
    count = count + 1;
    return count;
  };
  bump();
  return bump;
}
