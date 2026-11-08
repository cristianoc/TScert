// Pretext han-kerning: const-bound helpers and local arrows with checked bounds.
/** @requires safeInteger(i) && 0 <= i && i < xs.length */
const at = (xs: number[], i: number): number => xs[i]!,
  alsoAt = (xs: number[], i: number): number => xs[i]!;

export function readFirst(xs: number[]): number {
  /** @requires safeInteger(i) && 0 <= i && i < ys.length */
  const local = (ys: number[], i: number): number => { return ys[i]!; };
  if (xs.length > 0) return at(xs, 0) + alsoAt(xs, 0) + local(xs, 0);
  return 0;
}
