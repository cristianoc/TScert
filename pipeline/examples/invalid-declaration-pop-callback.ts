// A function declaration popping the array it is passed: its signature
// states no footprint keeping array stores, so the `map` callback calling it
// with the mapped array is not within one, `map` takes its unrestricted
// overload, and the result may hold holes.
function drop(xs: string[], t: string): string {
  xs.pop();
  return t;
}

export function dropped(ts: string[]): string[] {
  return ts.map((t) => drop(ts, t));
}
