// `fill(v, start)` fills from `start` only: index 0 stays a hole, which the
// loop reads as `undefined`, and `toFixed` throws a TypeError under Node.
// TypeScript types the result as `number[]`. Only `fill` of one argument is
// admitted.
export function digits(n: number): string {
  let text = "";
  for (const x of new Array<number>(n).fill(0, 1)) text += x.toFixed(0);
  return text;
}
