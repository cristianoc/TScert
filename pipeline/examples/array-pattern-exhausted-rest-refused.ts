// A rest after the iterator finished collects nothing: the hole's step finds
// the empty array's end, the default grows it, and the rest's steps still find
// the iterator finished. A collection from position 2 would hold 3.
export function restAfterGrow(): number[] {
  const xs: number[] = [];
  let a = 0;
  let rest: number[] = [];
  [, a = (xs.push(1, 2, 3), 9), ...rest] = xs;
  return [a, ...rest];
}
