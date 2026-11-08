// Index facts kept across a step whose writes cannot touch what they read
// (PROGRAM-TYPING.md, "Linear facts"): a field write's location held a member
// of the field's type, so it is no store a length reads (`cursorLoop`), no
// object a path reads and no number a path's last field holds where the type
// admits none (`labelled`, `counted`); and an element write below the length
// keeps every store's length (`filled`).

type Cursor = { i: number; label: string };
type Holder = { data: number[]; count: number };

export function cursorLoop(cur: Cursor, ys: number[]): number {
  let s = 0;
  for (let j = 0; j < ys.length; j++) {
    cur.i = j;
    s = s + ys[j]!;
  }
  return s;
}

/** @requires safeInteger(cur.i) && 0 <= cur.i && cur.i < xs.length */
export function labelled(cur: Cursor, xs: number[]): number {
  cur.label = "read";
  return xs[cur.i]!;
}

/** @requires safeInteger(i) && 0 <= i && i < o.data.length */
export function counted(o: Holder, i: number): number {
  o.count = i;
  return o.data[i]!;
}

export function filled(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    xs[i] = 1;
    s = s + xs[i]!;
  }
  return s;
}

// pretext's `segmentAtLineBreaks`: a write at `j + 1`, an index the facts
// bound below the length, keeps every length as a write at a binding does,
// so the loop keeps `count === flags.length`, which bounds its reads.
export function marked(flags: number[]): number {
  const count = flags.length;
  /** @invariant safeInteger(j) && safeInteger(count) && j + 2 <= count && count === flags.length */
  for (let j = count - 2; j >= 0; j--) {
    if ((flags[j]! & 15) === 8) continue;
    flags[j + 1] = flags[j + 1]! | 32;
  }
  return count;
}
