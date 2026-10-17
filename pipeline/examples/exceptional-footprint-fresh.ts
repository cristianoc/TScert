// A body allocating a fresh store and catching a throw: the handler binds
// the thrown value, never fresh, beside the slots the throwing node held,
// which keep their freshness, so the store `split` allocated may still be
// written in the handler.
function checked(x: number): number {
  if (x < 0) throw Error(`negative: ${x}`);
  return x;
}
export function counts(xs: string[], shift: number): number[] {
  return xs.map((s: string): number => {
    const pieces = s.split(",");
    try {
      return checked(pieces.length - shift);
    } catch {
      pieces.push("");
      return pieces.length;
    }
  });
}
