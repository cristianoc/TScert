// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#getExtraSpacings.
// Refusal: reject: source incoming edge obligation: the edge does not
// establish the claims at this point.
// A `for` loop whose update writes its bindings inside an expression
// (`start = ends[i++]`, here `start = i, i++`) holds them in cells the
// function allocates, and each statement entry restates their separation
// from the slots' locations. A binding given a call's result after the
// cells were allocated, `extras = zeros(count)`, holds an object no fact
// states apart from them: a callee cannot reach a cell the function never
// passes it, but the model states no reachability, and a source function's
// signature states no fresh result.
function zeros(count: number): number[] {
  return new Array<number>(count).fill(0);
}

export function extraSpacings(count: number): number[] {
  let extras: number[] = [];
  for (let i = 0, start = 0; i < count; start = i, i++) {
    if (extras.length === 0) extras = zeros(count);
    extras.push(start);
  }
  return extras;
}
