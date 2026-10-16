// A spread, or an object rest, of an array copies its own enumerable
// properties: its elements at their index keys, and any own field it
// carries, which at a canonical numeric key holds an element's type, as
// `Array<T>`'s declared `[n: number]: T` says. The copy holds the elements'
// type at every canonical numeric key.
export function restArrayEntries(source: number[]): number {
  const { ...copy } = source;
  if (Array.isArray(copy)) return 0;
  return copy[0] ?? 0;
}

export function spreadTuple(t: [string, number]): string | number | undefined {
  const copy = { ...t };
  return copy[1];
}
