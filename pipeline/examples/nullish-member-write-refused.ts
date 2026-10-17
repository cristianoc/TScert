// A plain write to a member of a value whose type admits `undefined` is
// refused: the guard is stated for reads, calls and updates, which read the
// member first.
type Box = { n: number };

export function reset(b: Box | undefined): number {
  // @ts-expect-error The box may be absent: the write throws there.
  b.n = 0;
  return 0;
}
