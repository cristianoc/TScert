// Reads at `i` and `i + 1` under the loop test `i + 1 < xs.length`, which
// entails both below the length: the loop's head claims `i ≤ 2^32 - 1`, a
// bound its entry states and its iteration entails by the length, so
// `i + 1` is a safe integer there. A loop to `e !== n` with `n` the length
// keeps `e ≤ n` alike, which its test's `true` answer makes strict.

export function pairProducts(xs: number[]): number {
  let s = 0;
  for (let i = 0; i + 1 < xs.length; i++) s = s + xs[i]! * xs[i + 1]!;
  return s;
}

export function nonzeroPrefix(xs: number[]): number {
  let e = 0;
  const n = xs.length;
  while (e !== n && xs[e]! !== 0) e++;
  return e;
}
