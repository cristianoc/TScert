export function mixed(xs: string[], x: number): number[] {
  // @ts-expect-error a spread of strings is no numbers
  return [x, ...xs];
}
