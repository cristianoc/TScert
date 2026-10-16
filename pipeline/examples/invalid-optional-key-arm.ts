// The other arm of the test: the key may be absent there.
function wrongArm(obj: { val?: number }): number {
  const r: number = obj.val === undefined ? obj.val : 0;
  return r;
}
