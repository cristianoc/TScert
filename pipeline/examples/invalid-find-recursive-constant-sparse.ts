// A recursive constant changing nothing, called by a `find` callback over
// an array lengthened past its elements: `find` visits the hole, handing
// the callback `undefined`, which the constant returns where a number is
// promised.
const count = (n: number, k: number): number => (k > 0 ? count(n, k - 1) : n);

export function wrong(): number {
  const xs: number[] = [1];
  xs.length = 2;
  return xs.findIndex((n) => typeof count(n, 1) !== "number");
}
