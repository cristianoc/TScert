// A value typed `(...args: never) => number` admits no argument list, an
// empty one included: calling it with none is refused. Under Node,
// `called(n => n)` returns undefined where a number is promised.
function called(f: (...args: never) => number): number {
  // @ts-expect-error: no argument list is a value of `never`
  return f();
}
export function run(): number {
  return called((n: number): number => n);
}
