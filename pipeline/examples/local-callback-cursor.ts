type Cursor = { i: number };

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length
 *  @ensures safeInteger(c.i) && 0 <= c.i */
function step(xs: number[], c: Cursor): Modifies<{ "c.*": "scalar" }, number> {
  const x = xs[c.i]!;
  c.i = c.i + 1;
  return x;
}

export function walk(xs: number[]): number {
  const c: Cursor = { i: 0 };
  const n = xs.length;
  let total = 0;
  while (true) {
    const s = c.i;
    if (s >= n) return total;
    total += step(xs, c);
  }
}

export function walkVisiting(
  xs: number[],
  onStep: (x: number) => void,
): number {
  const c: Cursor = { i: 0 };
  let total = 0;
  while (true) {
    const s = c.i;
    if (s >= xs.length) return total;
    const x = step(xs, c);
    total += x;
    onStep(x);
  }
}

export function cellFactAcrossCallback(
  v: string | number,
  onStep: (x: number) => void,
): string {
  const box: { v: string | number } = { v };
  if (typeof box.v === "string") {
    onStep(1);
    return box.v;
  }
  return "";
}

export function localArrayAcrossCallback(onStep: (x: number) => void): number {
  const buf = [10, 20, 30];
  onStep(buf[0]!);
  return buf[2]!;
}
