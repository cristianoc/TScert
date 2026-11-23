// The pattern of cristianoc/TScert#351, fixed by #353: a local copy of a
// field keeps its link to the field across a loop head when nothing in the
// loop changes the field.

// Accepted: nothing in the loop writes h.xs.
export function sumVia(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) s += xs[i]!;
  return s;
}

// Must stay refused: the body sets h.xs to a longer array, so the guard
// admits an index past the copy's end and xs[i] reads past it (unsafe).
export function sumViaWrites(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) {
    h.xs = [...xs, 0];
    s += xs[i]!;
  }
  return s;
}

function touch(h: { xs: number[] }): Modifies<{ values: "any" }, void> {
  h.xs = [];
}

// Must stay refused: the call may change h.xs, so the link does not survive
// it. (Safe, since the guard runs before the call: unprovable, not unsafe.)
export function sumViaCalls(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) {
    touch(h);
    s += xs[i]!;
  }
  return s;
}
