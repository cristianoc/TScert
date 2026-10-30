// The union's iteration steps an array as `%Iterate%` does, which requires
// a readable array: a `map` whose callback pops the array it maps has a
// hole, and the loop over it, beside a `Map`'s values, yields `undefined`
// there, no `number` (run under Node).
const shared: number[] = [1, 2, 3];
function drain(x: number): number {
  shared.pop();
  return x;
}

export function last(m: Map<string, number>, mapped: boolean): number {
  let n = 0;
  for (const v of mapped ? shared.map(drain) : m.values()) n = v;
  return n;
}
