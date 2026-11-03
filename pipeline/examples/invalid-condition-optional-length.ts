// `!o.p?.length && n > 3` is false where `o.p` is absent and `n` is at most
// 3: its cast is refused (`wrong({}, 0)` throws under Node).
export function wrong(
  o: { readonly p?: readonly string[] },
  n: number,
): number {
  if (!o.p?.length && n > 3) return 0;
  return (o.p as readonly string[]).length;
}
