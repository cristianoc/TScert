// A generic function type in an annotation is a scheme: a value of it meets
// its signature at every instance. A generic closure, a generic module
// function read as a value and a union of schemes.
function identity<T>(x: T): T {
  return x;
}

function label<T>(_x: T): string {
  return "label";
}

function keep<T extends string>(x: T): string {
  return x;
}

type Either = (<T>(x: T) => T) | (<T>(x: T) => string);

export function field(): void {
  const o: { fn: <T>(v: T) => T } = { fn: <T>(v: T) => v };
}

export function local(): string {
  const f: <T>(v: T) => T = identity;
  return f("a");
}

export function union(): void {
  const a: Either = identity;
  const b: Either = label;
}

// An impredicative instance: `T := <T>(x: T) => T`.
export function impredicative(): number {
  const f: <T>(x: T) => T = identity;
  const g: <U>(y: U) => U = f(identity);
  return g(1);
}

export function bounded(): string {
  const k = keep;
  return k("abc");
}
