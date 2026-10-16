export function pushAll<T>(first: T, ...rest: T[]): T[] {
  return [first, ...rest];
}
export function appended(xs: readonly number[], x: number): number[] {
  return [...xs, x];
}
export function joined(a: string[], b: readonly string[]): readonly string[] {
  return [...a, "-", ...b];
}
export function copy(xs: number[]): number[] {
  return [...xs];
}
export function withSet(s: Set<number>): number[] {
  return [0, ...s];
}
export function optional(xs: (number | undefined)[]): (number | undefined)[] {
  return [...xs, undefined];
}
function grow(xs: number[]): number {
  xs.push(7);
  return 8;
}
export function snapshot(): number {
  const xs = [1];
  const ys = [...xs, grow(xs)];
  return ys.length * 10 + xs.length;
}
export function testPushAll(): number[] {
  return pushAll(1, 2, 3);
}
export function inArrow(xs: number[]): (y: number) => number[] {
  return (y: number): number[] => [y, ...xs];
}
export function guarded(c: boolean, xs: number[]): number[] {
  if (c) return [1, ...xs];
  return [];
}
