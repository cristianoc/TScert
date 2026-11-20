// Two object literals two constants hold, the younger one's field facts
// stated at a loop's head: a write of the older one's field keeps them, the
// older constant holding a value bound before the younger allocation
// (`older`), and so does a write after a key-adding write rebinds the older
// constant to its copy, allocated later and apart from the younger object's
// named fields (`rebound`).
type C = { i: number };
type O = { i: number; j?: number };

export function older(xs: readonly number[]): number {
  const o: C = { i: 0 };
  const c: C = { i: 0 };
  let total = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    const s = c.i;
    c.i = s;
    o.i = -1;
    const x: number = xs[c.i]!;
    total = total + x;
    c.i = s + 1;
  }
  return total + o.i;
}

export function rebound(xs: readonly number[]): number {
  const o: O = { i: 0 };
  const c: C = { i: 0 };
  let total = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    const s = c.i;
    c.i = s;
    o.j = s;
    o.i = -1;
    const x: number = xs[c.i]!;
    total = total + x;
    c.i = s + 1;
  }
  return total + o.i;
}
