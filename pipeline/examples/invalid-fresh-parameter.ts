// `Fresh` at a parameter's type: it states a signature's result.
export function size(xs: Fresh<number[]>): number {
  return xs.length;
}
