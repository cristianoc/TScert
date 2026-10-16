// A method of Array.prototype, read through the array's prototype and called
// on the array: `reduce` with an initial value, at the element and the
// accumulator the call instantiates. The callback takes two of the four
// parameters `reduce` offers; the others are discarded when it is called.
function sum(xs: number[]): number {
  return xs.reduce((acc: number, x: number): number => acc + x, 0);
}
