// `p !== undefined || (q !== undefined && n > 0)` holds where `q` is
// defined and `n` positive, `p` undefined: its cast is refused
// (`wrong(undefined, "x", 1)` throws under Node).
export function wrong(
  p: string | undefined,
  q: string | undefined,
  n: number,
): number {
  if (p !== undefined || (q !== undefined && n > 0))
    return (p as string).length;
  return 0;
}
