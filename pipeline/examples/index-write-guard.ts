// A write at an index the program computes, behind the guard that checks it:
// the mask makes it an index, the comparison bounds it by the length, so the
// write lands on an element or appends (PROGRAM-TYPING.md, "Writes at a
// checked index"). Census functions: pretext's index writes (#94).
export function set(xs: number[], k: number, v: number): void {
  if ((k & 0x7fffffff) !== k || k > xs.length) throw new RangeError("index");
  xs[k] = v;
}

// At the length itself: an append.
export function append(xs: string[], v: string): void {
  const at = xs.length;
  if ((at & 0x7fffffff) !== at || at > xs.length) throw new RangeError("index");
  xs[at] = v;
}

// A read-modify-write, the index computed from others.
export function bump(counts: number[], i: number, from: number): void {
  const at = i - from;
  if ((at & 0x7fffffff) !== at || at > counts.length)
    throw new RangeError("index");
  counts[at] = (counts[at] ?? 0) + 1;
}
