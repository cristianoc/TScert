// A tuple is not a writable array: a write through the array could append
// past the tuple's length or store another element type. TypeScript accepts it.
export function widen(t: [number, number]): number[] {
  return t;
}
