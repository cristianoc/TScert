// The local state sits in a named helper the callback calls.
function count(s: string): number {
  let n = 0;
  for (let i = 0; i < s.length; i++) n = n + 1;
  return n;
}
export function counts(xs: readonly string[]): number[] {
  return xs.map((s: string): number => count(s));
}
