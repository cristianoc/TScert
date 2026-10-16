// `[^]` is a class of every character, so `|` splits the pattern: on "z"
// group 1 is unmatched.
export function first(s: string): string {
  const m = /[^]|x[](a)/.exec(s);
  return m ? m[1] : "";
}
