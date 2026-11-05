// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): gecko-line-breaks.ts#isEastAsianSegmentBreak,
// line-break.ts#walkPreparedComplexLines.
// A `let` declared without an initializer, assigned before every exit of a
// loop whose head tests nothing (`for (;;)`) or of a `do` loop, and read
// after the loop: the head's test is the constant `true`, whose `false`
// edge no run takes, so the loop is left only by a `break` or by the test
// after the body, each where the binding holds a number.
function scaled(n: number): number {
  return n * 2;
}

export function firstAbove(xs: number[], limit: number): number {
  let found: number;
  for (let i = 0; ; i++) {
    if (i >= xs.length) {
      found = -1;
      break;
    }
    const x = xs[i];
    if (x !== undefined && x > limit) {
      found = i;
      break;
    }
  }
  return scaled(found);
}

export function lastBelow(text: string, end: number): number {
  let code: number;
  let at = end;
  do {
    code = text.charCodeAt(at - 1);
    at--;
  } while (code === 0x20 && at > 0);
  return scaled(code);
}
