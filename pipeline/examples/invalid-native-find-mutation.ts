// find visits the original range: shrinking the array passes undefined to the next callback.
export function wrong(xs: number[], seen: { value: number }): number {
  xs.find((x: number): boolean => {
    seen.value = x;
    xs.pop();
    return false;
  });
  return seen.value;
}
