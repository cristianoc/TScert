// A boxed number as the indent is converted by its `valueOf`, client code
// `JSON.stringify` runs (run under Node): the stated indent is a primitive
// number or string.
interface Counted {
  valueOf(): number;
}

export function spaced(x: number, space: Counted): string {
  // @ts-expect-error: an object is no number
  return JSON.stringify(x, null, space);
}
