// `Object.keys` is a fresh array of the object's own enumerable string keys,
// whatever its type says of them; `Object.values` and `Object.entries` read
// the values of those keys, of which nothing is known.
interface Point {
  x: number;
  y: number;
}

function names(o: { a: number }, p: Point): string[] {
  const fromInterface: string[] = Object.keys(p);
  return Object.keys(o);
}

function contents(p: Point): unknown[] {
  const pairs: [string, unknown][] = Object.entries(p);
  return Object.values(p);
}
