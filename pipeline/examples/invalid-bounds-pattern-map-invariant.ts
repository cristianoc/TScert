// Bounds pattern P20, the unsafe neighbour of
// `bounds-pattern-map-invariant-refused`: a value of the `Map` set by
// another function, one element long (run under Node after `poison("x")`:
// `undefined` at `number`). A type contract must be proved at every
// construction of the type.
/** @invariant this.index.length === 4352 */
export type ClassTable = { readonly index: Uint16Array };

const cache = new Map<string, ClassTable>();

export function poison(name: string): void {
  cache.set(name, { index: new Uint16Array(1) });
}

/** @requires safeInteger(c) && 0 <= c && c < 1114112 */
export function classOf(name: string, c: number): number {
  const t = cache.get(name);
  return t === undefined ? 0 : t.index[c >> 8]!;
}
