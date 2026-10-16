// An ambient function's result is its declared type, not another.
declare function double(x: number): number;
export function wrong(x: number): boolean {
  return double(x);
}
