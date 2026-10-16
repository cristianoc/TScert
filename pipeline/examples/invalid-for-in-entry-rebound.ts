// The loop enumerates the object `v` held at its start; rebinding `v` in its
// body makes a later iteration read another object at a key of the first,
// which it may lack.
export function wrong(
  v: { [k: string]: number },
  other: { [k: string]: number },
): number {
  let last: number = 0;
  for (const k in v) {
    last = v[k]!;
    v = other;
  }
  return last;
}
