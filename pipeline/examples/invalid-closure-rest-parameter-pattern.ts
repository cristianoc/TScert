// A closure's rest parameter pattern: the rest binds one name.
export function firstOf(): (...xs: number[]) => number | undefined {
  return (...[a]: number[]): number | undefined => a;
}
