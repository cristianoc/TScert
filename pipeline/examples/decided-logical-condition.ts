// Conditions decided by a constant operand of `||` and `&&`: `true || flag`
// always holds and `false && flag` always fails, so the arm each rules out
// is one no run takes, and a `let` assigned in the arm taken holds a number
// after the statement, as it does after the `while (true || flag)` loop
// left only by its `break`.
function scaled(n: number): number {
  return n * 2;
}

export function eitherHolds(flag: boolean, seed: number): number {
  let picked: number;
  if (true || flag) {
    picked = seed;
  }
  return scaled(picked);
}

export function bothFail(flag: boolean, seed: number): number {
  let picked: number;
  if (false && flag) {
    scaled(seed);
  } else {
    picked = seed;
  }
  return scaled(picked);
}

export function loopUntilBreak(flag: boolean, seed: number): number {
  let picked: number;
  while (true || flag) {
    picked = seed;
    break;
  }
  return scaled(picked);
}
