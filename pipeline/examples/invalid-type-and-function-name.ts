// The type `Pair` holds numbers, whatever the function of its name returns.
type Pair = { first: number; second: number };
function Pair(first: number, second: number): Pair {
  return { first, second };
}
function first(): string {
  const p: Pair = Pair(1, 2);
  const s: string = p.first;
  return s;
}
