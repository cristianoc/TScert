// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// gecko-line-breaks.ts#markWordBreaks.
// Refusal: gate: statement outside the fragment (LabeledStatement).
// A labeled loop left by `break outer` from a nested loop: a labeled
// statement is outside the fragment.
export function firstPair(xs: number[]): number {
  let found = -1;
  outer: for (let i = 0; i < xs.length; i++) {
    for (let j = i + 1; j < xs.length; j++) {
      if (xs[i] === xs[j]) {
        found = i;
        break outer;
      }
    }
  }
  return found;
}
