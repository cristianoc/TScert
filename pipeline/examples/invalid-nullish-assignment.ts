// The right side of `??=` is written at the target's contract.
function fill(o: { n: number | undefined }): number {
  o.n ??= "seven";
  return 0;
}
