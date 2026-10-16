// A module function without a rest parameter discards the actuals past its
// parameters, so it meets a signature binding more parameters whose leading
// ones its own accept: as a result, an annotated binding, an argument, an
// intersection's member and a variadic signature.
function one(_x: number): string {
  return "one";
}
function none(): string {
  return "none";
}
function optional(x?: number): number {
  return x ?? 0;
}
export function widen(): (a: number, b: string) => string {
  return one;
}
export function bound(): string {
  const two: (a: number, b: string) => string = one;
  return two(1, "b");
}
function each(f: (x: number, i: number) => string): string {
  return f(1, 2);
}
export function passed(): string {
  return each(one);
}
export function both(): (() => string) & ((x: number) => string) {
  return none;
}
export function variadic(): (a: number, ...args: readonly string[]) => number {
  return optional;
}
export function contravariant(): (a: 1, b: boolean, c: null) => string {
  return one;
}
