// Generic bodies under bounds of any ground type, with unions that mention a
// binder, a closure whose result the source leaves to inference, an
// expression statement, and a body that falls off its end.
function asString<T extends string>(x: T): string {
  return x;
}
function chain<T extends string | number, U extends T>(x: U): T {
  const y: T = x;
  return y;
}
function either<T>(x: T, fallback: string | T): string | T {
  const y: string | T = x;
  return fallback;
}
function optional<T>(input: T, arg?: T): T | undefined {
  return arg;
}
function adder<T>(input: T): (arg: T) => T {
  return (arg: T) => arg;
}
function ignored<T>(x: string | T): void {}
function feed<T>(f: (x: T) => void, x: T): void {
  f(x);
}

export function callers(s: "a", n: number): string | number {
  ignored(n);
  feed((m: number): void => {}, n);
  const f = adder<number>(n);
  const k = optional(n);
  const e = either(n, "b");
  return asString(s) + chain<string | number, "c">("c");
}
