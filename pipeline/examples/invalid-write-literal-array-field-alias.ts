export function write(
  target: { values: (number | string)[] },
  values: number[],
): void {
  target.values = values;
}
