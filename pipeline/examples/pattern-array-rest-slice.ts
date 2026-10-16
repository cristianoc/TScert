// A rest TypeScript types as no one tuple of required positions is a slice:
// `%RestFrom:k%`, after the pattern's `k` elements, collects the elements
// from `k` to the array's current length into a fresh array. Over a union of
// tuples of different lengths each arm meets its parameter on its own, so
// the rest holds what the arms hold from `k` on.
export function restFromArray(arr: number[]): number[] {
  const [first, ...rest] = arr;
  const a: number | undefined = first;
  return rest;
}

export function unionRest(source: [number] | [number, string]): string[] {
  const [head, ...tail] = source;
  return tail;
}

export function optionalRest(
  source: [number, string?],
): (string | undefined)[] {
  const [, ...tail] = source;
  return tail;
}

export function assigned(src: number[]): number[] {
  let x: number | undefined = 0;
  let r: number[] = [];
  [x, ...r] = src;
  return r;
}

export function genericAssigned<T>(source: [number] | [number, T]): T[] {
  let head: number | T | undefined = 0;
  let tail: T[] = [];
  [head, ...tail] = source;
  return tail;
}

export function parameter([first, ...others]: readonly boolean[]): boolean[] {
  return others;
}
