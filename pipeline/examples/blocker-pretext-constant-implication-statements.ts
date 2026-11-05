// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#measureFitAdvances,
// measurement.ts#getSegmentFit.
// Refusal: reject: source incoming edge obligation: the edge does not
// establish the claims at this point (`prefixes` boolean, `true` required).
// A constant holding a comparison of a literal union, `prefixes = from ===
// "a"`, tested statements later and inside a loop: the constant's
// implication reaches each statement's entry from the edges entering it,
// and a loop's head from its entry edge, which the back edge then confirms.
function onlyA(from: "a"): number {
  return from.length;
}

export function advances(count: number, from: "a" | "b"): number {
  const prefixes = from === "a";
  let total = 0;
  total = 1;
  total = 2;
  for (let i = 0; i < count; i++) {
    if (prefixes) total = onlyA(from);
  }
  return total;
}
