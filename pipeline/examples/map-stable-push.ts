// A callback that pushes onto an array it just created.
export function twice(xs: readonly number[]): number[][] {
  return xs.map((x: number): number[] => {
    const a: number[] = [];
    a.push(x);
    a.push(x);
    return a;
  });
}
