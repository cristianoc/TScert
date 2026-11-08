// Pretext: measurement.ts#measureFitAdvances, advances.length === i.
export function build(xs: string[]): string[] {
  const out: string[] = [];
  /** @invariant safeInteger(i) && 0 <= i && out.length === i */
  for (let i = 0; i < xs.length; i++) out.push(xs[i]!);
  return out;
}
export function twice(xs: string[]): string {
  const n = xs.length;
  xs.push("a", "b");
  return xs[n + 1]!.toUpperCase();
}
