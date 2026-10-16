// Under the ordinary-construction invariant, these natives create arrays.
// The runtime boundary controls deliberately supply inputs outside that invariant.
export function mappedLength(xs: number[]): number {
  return xs.map((x: number): number => x).length;
}

export function filteredLength(xs: number[]): number {
  return xs.filter((x: number): boolean => x > 0).length;
}

export function slicedArray(xs: number[]): number[] {
  return xs.slice();
}

// An ordinary record may still have a writable field called constructor.
export function recordConstructor(
  obj: { constructor: number },
  value: number,
): number {
  obj.constructor = value;
  return obj.constructor;
}
