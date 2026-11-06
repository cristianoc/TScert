// A `let` with no initializer, assigned before the one `break` of a
// `for (;;)` loop whose body also `continue`s, read after the loop: the
// `continue` returns to the head, whose `false` edge no run takes.
function scaled(n: number): number {
  return n * 2;
}

export function firstPositive(xs: number[]): number {
  let found: number;
  for (let i = 0; ; i++) {
    const x = xs[i];
    if (x === undefined) {
      found = 0;
      break;
    }
    if (x <= 0) {
      continue;
    }
    found = x;
    break;
  }
  return scaled(found);
}
