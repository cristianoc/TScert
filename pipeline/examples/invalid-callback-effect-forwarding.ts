// Forwarding an ordinarily annotated mutating callback must not manufacture a preservation guarantee.
export function wrong(xs: number[]): number[] {
  const shrink: () => number = (): number => {
    xs.pop();
    return 1;
  };
  return xs.map((_value: number): number => shrink());
}
