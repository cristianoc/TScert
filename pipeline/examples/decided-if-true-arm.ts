// A `let` assigned only in the arm `if (true)` takes, read after the
// statement: the other arm's edge is one no run takes, so after the `if` the
// binding holds a number.
function scaled(n: number): number {
  return n * 2;
}

export function chosen(seed: number): number {
  let picked: number;
  if (true) {
    picked = seed + 1;
  } else {
    scaled(seed);
  }
  return scaled(picked);
}
