// Ordinary construction gives a sparse map result its numeric length,
// including after callback mutation.
export function mappedLength(xs: number[]): number {
  return xs.map((x: number): number => {
    xs.pop();
    return x;
  }).length;
}

// The original repair-corpus example: tuple methods survive a typeof branch.
export function testTupleArrayMethod(x: [number, string] | number): number {
  if (typeof x === "object") {
    return x.map((v: number | string) => v).length;
  } else {
    return x;
  }
}
