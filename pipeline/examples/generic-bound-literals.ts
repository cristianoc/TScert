// Instances TypeScript infers at a bounded binder: a fresh object literal at
// `T extends Json` is allocated at the bound's dictionary arm, a writable one,
// and primitives below a bound are the binder, not the bound.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };

function keep<T extends Json>(x: T): T {
  return x;
}
export function literal(): Json {
  return keep({ name: "test", nested: { value: 42 } });
}

function check<Y extends boolean | string>(x: Y): Y {
  return x;
}
function id<X>(x: X): X {
  return x;
}
export function primitive(): string {
  const a = id("hello");
  const b = check(a);
  return b;
}

// An array of primitives below a bound with an array arm is the binder too.
function either<S extends number[] | string>(values: S): S {
  return values;
}
export function array(): number | undefined {
  const result = either([1, 2, 3]);
  return result[0];
}
