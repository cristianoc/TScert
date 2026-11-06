// A `let` with no initializer, assigned before each `break` of a
// `while (true)` loop, read after the loop: the head's `false` edge is one no
// run takes, so the loop is left only by a `break`, each where the binding
// holds a number.
function scaled(n: number): number {
  return n * 2;
}

export function firstZero(xs: number[]): number {
  let at: number;
  let i = 0;
  while (true) {
    if (i >= xs.length) {
      at = -1;
      break;
    }
    if (xs[i] === 0) {
      at = i;
      break;
    }
    i++;
  }
  return scaled(at);
}
