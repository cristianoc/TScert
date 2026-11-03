// `!s && n > 3` is false where `s` is undefined and `n` is at most 3: there
// `s` is no string, and its cast is refused (`wrong(undefined, 0)` throws
// under Node).
export function wrong(s: string | undefined, n: number): number {
  if (!s && n > 3) return 0;
  return (s as string).length;
}
