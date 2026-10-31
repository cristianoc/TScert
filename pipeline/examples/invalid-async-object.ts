// unchecked.mts#findIn, #check and #decodeResult include runPart, which
// returns a freshly decoded record through its declared result type.
// The lifetime then contract retains what the fresh allocation establishes.
type Result = { a: number; readonly then?: undefined };

function decode(a: number): Result {
  return { a };
}

export async function wrap(a: number): Promise<Result> {
  const result = decode(a);
  return result;
}
