// A record seen through Partial: writing undefined through the alias would
// leave the original's required field undefined.
export function clear(t: { a: number }): number {
  const p: Partial<{ a: number }> = t;
  p.a = undefined;
  return t.a;
}
