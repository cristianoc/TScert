// `p === undefined && n` is false where `p` is undefined and `n` is 0:
// there `p` is no string, and its cast is refused (`wrong(undefined, 0)`
// throws under Node).
export function wrong(p: string | undefined, n: number): number {
  if (p === undefined && n) return 0;
  return (p as string).length;
}
