// An array literal keeps what was known of the heap, but a write after it
// still changes the field: it holds 2, not the 1 the guard found.
export function changed(x: { f: 1 | 2 }): 1 {
  if (x.f === 1) {
    const xs = [x.f];
    x.f = 2;
    return xs.length > 0 ? x.f : 1;
  }
  return 1;
}
