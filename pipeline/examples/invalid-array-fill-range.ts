// `fill(v, start, end)` fills below `end` only: index 1 of a longer array
// stays a hole, which the loop reads as `undefined`, and `toFixed` throws a
// TypeError under Node. TypeScript types the result as `number[]`. Only
// `fill` of one argument is admitted.
export function digits(n: number): string {
  let text = "";
  for (const x of new Array<number>(n).fill(0, 0, 1)) text += x.toFixed(0);
  return text;
}
