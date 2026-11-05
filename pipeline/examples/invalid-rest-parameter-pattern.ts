// A rest parameter's pattern: the rest binds one name.
export function first(...[a]: number[]): number | undefined {
  return a;
}
