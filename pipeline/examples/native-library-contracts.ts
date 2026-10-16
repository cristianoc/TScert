// Native callbacks may mutate through aliases; primitive conversion runs no client code.
export function guarded(xs: number[], seen: { value: number }): number {
  xs.find((x: number | undefined): boolean => {
    seen.value = x ?? 0;
    xs.pop();
    return false;
  });
  return seen.value;
}
export function mapped(xs: number[]): unknown {
  return xs.map((x: number): number => {
    xs.pop();
    return x;
  });
}
export function primitives(xs: number[]): string {
  xs.sort();
  return xs.join(",");
}
