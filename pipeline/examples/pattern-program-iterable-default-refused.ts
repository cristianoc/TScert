// A default in an array pattern over a program's iterable runs between the
// iterator's steps, and a throw of it closes the iterator: the lowering binds
// the names after the steps.
function fallback(): number {
  return 0;
}

export function first(values: Iterable<number>): number {
  const [a = fallback()] = values;
  return a;
}
