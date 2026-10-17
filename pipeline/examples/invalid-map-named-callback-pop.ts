// A module function passed by name as a `map` callback, popping the array it
// is given: `pop` bounds it by nothing, so `map` takes its signature with
// holes.
const shared: number[] = [1, 2, 3];
function drain(x: number): number {
  shared.pop();
  return x;
}

export function drained(): number[] {
  return shared.map(drain);
}
