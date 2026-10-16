// A method declaring `this: T` is a member whose host must meet `T`: read
// from a host that is a `T` and invoked on it, it behaves as typed. The
// method's body reads its receiver at `T`; a call checks the host against it.
class Ctx {
  value: number = 1;
}
class Holder {
  m(this: Ctx, x: number): number {
    return this.value + x;
  }
}
export function call(h: Holder & Ctx): number {
  return h.m(1);
}
export function bracket(h: Holder & Ctx): number {
  return h["m"](2);
}
// A type literal's method states it alike.
export function literal(o: Ctx & { m(this: Ctx, x: number): number }): number {
  return o.m(3);
}
// A subclass instance is a host of a method whose receiver is its base.
class Base {
  tag: string = "base";
}
class Derived extends Base {}
class BaseMethod {
  m(this: Base): string {
    return this.tag;
  }
}
export function derived(d: Derived & BaseMethod): string {
  return d.m();
}
// The class's own instance meets a receiver it is within.
class Counter {
  count: number = 0;
  current(this: { count: number }): number {
    return this.count;
  }
  next(): number {
    return this.current() + 1;
  }
}
export function counted(): number {
  return new Counter().next();
}
