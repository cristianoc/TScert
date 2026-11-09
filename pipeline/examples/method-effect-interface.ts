// An interface member stating the empty footprint: an object literal's
// method meets it, and a `findIndex` callback calling it changes no store,
// so each visit reads an element of the array's contract (`T`, not
// `T | undefined`).
export interface Limit {
  over(n: number): Modifies<{}, boolean>;
}

export function firstOver(limit: Limit, xs: number[]): number {
  return xs.findIndex((x) => limit.over(x));
}

export function overTen(xs: number[]): number {
  return firstOver(
    {
      over(n: number): Modifies<{}, boolean> {
        return n > 10;
      },
    },
    xs,
  );
}
