// The loop enumerates the object `o.inner` held at its start; a write of
// `o.inner` in its body makes a later iteration read another object at a key
// of the first, which it may lack.
export function wrong(
  o: { inner: { [k: string]: number } },
  other: { [k: string]: number },
): number {
  let last: number = 0;
  for (const k in o.inner) {
    last = o.inner[k]!;
    o.inner = other;
  }
  return last;
}
