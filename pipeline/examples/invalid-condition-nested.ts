// `!(!(p !== undefined) && !(q !== undefined))` holds where either is
// defined: `p` may be undefined there, and its cast is refused
// (`wrong(undefined, "x")` throws under Node).
export function wrong(p: string | undefined, q: string | undefined): number {
  if (!(!(p !== undefined) && !(q !== undefined))) return (p as string).length;
  return 0;
}
