// A namespace import used through member reads and qualified type names reads
// each member as a binding of its own, the export TypeScript binds it to:
// values at their declared types, types at their declarations.
import * as lib from "@fixture/lib";
import * as lib$limit from "@fixture/lib";

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

// A member read as a value and then called passes no receiver.
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

// `lib.limit$double` and `lib$limit.double` are two members of two
// namespaces: 3, and `double` of 1.
export function twoMembers(): number {
  return lib.limit$double + lib$limit.double(1);
}

// A member read written across lines is one member read.
export function spaced(): number {
  // prettier-ignore
  return lib
    .double(2);
}
