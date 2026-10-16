// `reduce` returns its accumulator's type, a number here: a function
// promising a boolean from it is refused.
function sum(xs: number[]): boolean {
  return xs.reduce(
    (acc: number, x: number, i: number, all: readonly number[]): number =>
      acc + x,
    0,
  );
}
