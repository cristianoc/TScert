// Past `(c && x) || (!c && p === undefined)` with `c` true, `x` failed and
// says nothing of `p`: its cast is refused (`wrong(true, undefined, false)`
// throws under Node).
export function wrong(c: boolean, p: string | undefined, x: boolean): number {
  if ((c && x) || (!c && p === undefined)) return 0;
  return c ? (p as string).length : 1;
}
