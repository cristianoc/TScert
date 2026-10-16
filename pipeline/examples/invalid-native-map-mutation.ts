// map can leave holes when its callback shrinks the source; the result is not a dense array.
export function wrong(xs: number[], seen: { value: number }): number {
  const ys = xs.map((x: number): number => {
    xs.pop();
    return x;
  });
  for (const y of ys) {
    seen.value = y;
  }
  return seen.value;
}
