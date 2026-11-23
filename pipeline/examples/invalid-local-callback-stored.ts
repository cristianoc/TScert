type Cursor = { i: number };
type Holder = { cur: Cursor | null };

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length
 *  @ensures safeInteger(c.i) && 0 <= c.i */
function step(xs: number[], c: Cursor): Modifies<{ "c.*": "scalar" }, number> {
  const x = xs[c.i]!;
  c.i = c.i + 1;
  return x;
}

export function walkStored(
  xs: number[],
  holder: Holder,
  onStep: (x: number) => void,
): number {
  const c: Cursor = { i: 0 };
  holder.cur = c;
  let total = 0;
  while (true) {
    const s = c.i;
    if (s >= xs.length) return total;
    const x = step(xs, c);
    total += x;
    onStep(x);
  }
}
