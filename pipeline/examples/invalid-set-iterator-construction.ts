// `new Set` of an iterator: TypeScript resolves the iterable overload, whose
// stated forms take an array or a string; an iterator is neither, and a
// client iterator would run code.
export function keysOf(m: Map<string, number>): number {
  return new Set(m.keys()).size;
}
