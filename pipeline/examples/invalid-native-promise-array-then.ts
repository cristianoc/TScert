export function length(
  values: number[] & { then: (resolve: (value: number) => void) => void },
): number {
  return values.length;
}
