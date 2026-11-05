// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#getSegmentFit.
// A constant holding a comparison, tested as the left operand of `&&`: the
// branch on the constant narrows `from` where it is `true`, and the right
// operand's nodes run in that narrowing, so the call in the arm reads `from`
// at "a". The constant's condition is read as its tests run it, the
// equality with the literal a tag test of `from`.
function onlyA(from: "a"): number {
  return from.length;
}

export function fit(from: "a" | "b", n: number): number {
  const prefixes = from === "a";
  if (prefixes && n > 2) return onlyA(from);
  return 0;
}
