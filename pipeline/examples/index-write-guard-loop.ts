// Writes behind the guard in a loop, forward and reverse; the bound reaches
// each iteration's write from the guard before it.
export function clear(xs: number[]): void {
  for (let j = 0; j < xs.length; j++) {
    if ((j & 0x7fffffff) !== j || j > xs.length) throw new RangeError("index");
    xs[j] = 0;
  }
}

export function fillBack(xs: (string | null)[], v: string): void {
  for (let k = xs.length - 1; k >= 0; k--) {
    if ((k & 0x7fffffff) !== k || k > xs.length) throw new RangeError("index");
    xs[k] = v;
  }
}
