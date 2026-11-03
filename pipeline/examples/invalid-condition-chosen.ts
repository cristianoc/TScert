// The false arm of `p !== undefined ? n > 0 : …` runs where `p` is
// undefined: its cast there is refused (`wrong(undefined, 0)` throws under
// Node).
function len(s: string): number {
  return s.length;
}
export function wrong(p: string | undefined, n: number): number {
  if (p !== undefined ? n > 0 : len(p as string) > 2) return 1;
  return 0;
}
