// Writes and allocations keyed by a `unique symbol` constant other than the
// tag are admitted: the key's one value is no `Symbol.toStringTag`.
const mark: unique symbol = Symbol("mark");

export function rewrite(d: { [mark]: number }): number {
  d[mark] = 2;
  return d[mark];
}

export function make(): { [mark]: number } {
  return { [mark]: 1 };
}
