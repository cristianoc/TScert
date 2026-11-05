// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#getSegmentFit.
// Refusal: reject: source incoming edge obligation: the edge does not
// establish the claims at this point (`from` is "a" | "b", "a" required).
// A constant holding a comparison, tested as the left operand of `&&`: the
// branch on the constant narrows `from` on its edge, but the nodes of the
// right operand are claimed at the statement's entry, where `from` is
// "a" | "b". The constant alone, or as the right operand, narrows.
function onlyA(from: "a"): number {
  return from.length;
}

export function fit(from: "a" | "b", n: number): number {
  const prefixes = from === "a";
  if (prefixes && n > 2) return onlyA(from);
  return 0;
}
