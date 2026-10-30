// A call of a member read through `!`, `as` or `satisfies` passes the
// member's object as its receiver: the emit erases the wrappers, and the
// parentheses keep the reference. The object is evaluated once and saved,
// the member read off it as a value (each annotation checked on that value),
// then called with the saved object as `this` (run under Node).
interface Counter {
  readonly base: number;
  readonly add: (this: Counter, x: number) => number;
}
type Add = (this: Counter, x: number) => number;

export function asserted(c: Counter, x: number): number {
  return c.add!(x);
}

export function cast(c: Counter, x: number): number {
  return (c.add as Add)(x);
}

export function checked(c: Counter, x: number): number {
  return (c.add satisfies Add)(x);
}

export function keyed(c: Counter, x: number): number {
  return c["add"]!(x);
}

export function chained(c: Counter | undefined, x: number): number | undefined {
  return c?.add!(x);
}

export function once(make: () => Counter, x: number): number {
  return make().add!(x);
}
