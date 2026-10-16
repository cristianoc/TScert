// A closure parameter written without a type is at the type TypeScript gives
// it from its context: a library callback's element, a declared callback's
// parameter, a declaration by name, a type parameter. The body is checked at
// that type, and the closure's signature where the call receives it.
interface User {
  name: string;
}
declare function withCallback(cb: (n: number) => number): void;
export function sorted(a: number[]): number[] {
  return a.slice().sort((x, y) => x - y);
}
export function each(a: string[]): void {
  a.forEach((s, i) => {
    const _s: string = s;
    const _i: number = i;
  });
}
export function declared(): void {
  withCallback((n) => n + 1);
}
export function names(us: User[]): string[] {
  return us.map((u) => u.name);
}
export function kept<T>(xs: T[]): T[] {
  return xs.filter((x) => x !== undefined);
}
const double: (n: number) => number = (n) => n * 2;
export function doubled(xs: number[]): number[] {
  return xs.map((x) => double(x));
}
