// An optional parameter is a position the longer signature writes: its actual
// must be within the parameter's type, here a number at a string.
function opt(x: number, y?: string): string {
  return y === undefined ? String(x) : y.toUpperCase();
}
export function widen(): (a: number, b: number, c: string) => string {
  return opt;
}
