// A split splices its captures in, an unmatched one as `undefined`:
// "a1b".split(/(\d)|(x)/) is ["a", "1", undefined, "b"].
export function parts(s: string): string[] {
  return s.split(/(\d)|(x)/);
}
