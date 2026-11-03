// `p && n` is `p` where `p` is the empty string: its cast to a number is
// refused (`wrong("", 1)` throws under Node).
export function wrong(p: string | undefined, n: number): string {
  const v = p && n;
  return (v as number).toFixed();
}
