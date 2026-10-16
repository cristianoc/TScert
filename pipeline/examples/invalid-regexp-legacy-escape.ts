// Outside Unicode mode `\k` is the letter k where no group is named, so the
// brackets hide no alternative: on "k<a" group 1 is unmatched.
export function first(s: string): string {
  const m = /\k<a|x>(b)/.exec(s);
  return m ? m[1] : "";
}
