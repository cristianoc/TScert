// A `map` callback spreading into a function that pops the array being
// mapped: the call is bounded by `pop`, so `map` takes its signature with
// holes.
const shared: number[] = [1, 2, 3];
function total(...xs: number[]): number {
  shared.pop();
  return xs.length;
}

export function totals(rows: number[][]): number[] {
  return shared.map((x: number): number => total(...(rows[0] ?? []), x));
}
