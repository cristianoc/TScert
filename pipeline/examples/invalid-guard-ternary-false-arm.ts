// A guard's call answering `false` narrows nothing on a conditional's second
// arm: TypeScript reads `x` there as "b", but the guard may answer `false` of
// "a" (run under Node: `wrong("a")` is "a" where "b" is promised).
function isA(x: "a" | "b"): x is "a" {
  return x === "a" && false;
}
function onlyB(x: "b"): "b" {
  return x;
}
export function wrong(x: "a" | "b"): "b" | 0 {
  return isA(x) ? 0 : onlyB(x);
}
