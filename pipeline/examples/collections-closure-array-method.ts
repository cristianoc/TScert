// Plus and a sorted reduction: array methods called inside a method.
class Summer {
  sum(xs: number[]): number {
    return xs.reduce((p: number, c: number): number => p + c, 0);
  }
  sorted(xs: number[]): number {
    return xs.sort().reduce((p: number, c: number): number => p + c, 0);
  }
}
export function use(xs: number[]): number {
  return new Summer().sum(xs) + new Summer().sorted(xs);
}
