// A namespace import used through member reads and qualified type names is
// the named import of each member: values at their declared types, types at
// their declarations.
import * as lib from "@fixture/lib";

export function doubled(): number {
  return lib.double(lib.limit);
}

export function unwrapped(n: number): number {
  const b: lib.Branded = lib.wrap(n);
  return lib.unwrap(b);
}

export function counted(c: lib.Counter): number {
  return c.bump();
}

// A member read as a value and then called passes no receiver, as the named
// import's call does.
export function held(): number {
  const f = lib.double;
  return f(2);
}

// A binding of the same name shadows the namespace: its reads are its own.
export function shadowed(lib: { limit: string }): string {
  return lib.limit;
}

// A value's type through the namespace: `typeof lib.limit` is `number`.
export function typed(): number {
  const n: typeof lib.limit = lib.limit;
  return n;
}
