// Issue #364.
// When loop-head settling runs a diagnosing walk (`lackingAt`), it must run
// with the same checker layer as the pass itself; otherwise the diagnosing
// walk drops a handle-length fact kept across a bounded callback's call.

type Footprint = {
  [location: string]:
    | "keep"
    | "init"
    | "scalar"
    | "extend"
    | "grow"
    | "any"
    | true;
};
type AtMost<P extends Footprint> = Footprint;
type Visitor<E extends Footprint> = (v: number) => Modifies<E, void>;
type Handle = { xs: number[] };
type Counter = { count: number };

/** @requires safeInteger(i) && 0 <= i && i < h.xs.length */
function readAt(h: Handle, i: number): Modifies<{}, number> {
  return h.xs[i]!;
}

function bump(c: Counter): Modifies<{ "c.*": "scalar" }, void> {
  c.count++;
}

// Accepted by the prototype: `c.count === 0` is carried to the loop head and
// falsified by `bump(c)`, so loop-head settling runs `lackingAt`. With the
// checker layer, `lackingAt` keeps `n === h.xs.length` across `onStep?.(v)`.
export function walkSettling<E extends AtMost<{ "h.**": "keep"; else: "any" }>>(
  h: Handle,
  onStep?: Visitor<E>,
): number {
  const c: Counter = { count: 0 };
  const n = h.xs.length;
  let i = 0;
  let total = 0;
  /** @invariant safeInteger(i) && 0 <= i */
  while (true) {
    if (i >= n) return total;
    const v = readAt(h, i);
    total += v;
    bump(c);
    onStep?.(v);
    i++;
  }
}

// Negative, unsafe: the bound does not keep `h.**`, so `onStep` may pop
// `h.xs` and leave `n` past `h.xs.length`.
export function walkUnbounded<E extends AtMost<{ else: "any" }>>(
  h: Handle,
  onStep?: Visitor<E>,
): number {
  const c: Counter = { count: 0 };
  const n = h.xs.length;
  let i = 0;
  let total = 0;
  /** @invariant safeInteger(i) && 0 <= i */
  while (true) {
    if (i >= n) return total;
    const v = readAt(h, i);
    total += v;
    bump(c);
    onStep?.(v);
    i++;
  }
}
