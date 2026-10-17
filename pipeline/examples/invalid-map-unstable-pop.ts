// Negative control: the callback shrinks the array map is reading,
// so the result has a hole where number[] promises a number.
export function shrink(xs: number[]): number[] {
  return xs.map((x: number): number => {
    xs.pop();
    return x;
  });
}
