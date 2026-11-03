// Splice copies removed values, inserts evaluated arguments and changes only
// its receiver's existing store. Offset conversion uses primitive numbers.
export function insert(
  xs: string[],
  start: number,
  count: number,
  items: readonly string[],
): string[] {
  return xs.splice(start, count, ...items);
}
export function omitted(xs: number[]): number[] {
  return xs.splice(1);
}
export function explicitUndefined(xs: number[]): number[] {
  return xs.splice(1, undefined);
}
export function objects(
  xs: { value: number }[],
  items: { value: number }[],
): { value: number }[] {
  return xs.splice(0, xs.length, ...items);
}
export function holes(
  xs: (string | undefined)[],
  items: (string | undefined)[],
): (string | undefined)[] {
  return xs.splice(0, 2, ...items);
}
export function ordered(xs: number[], later: () => number): number[] {
  return xs.splice(0, 1, ...xs, later());
}
export function local(xs: readonly number[]): number[] {
  return xs.map((x) => {
    const values = xs.slice();
    const removed = values.splice(0, 1, x, x);
    removed.pop();
    return x;
  });
}
