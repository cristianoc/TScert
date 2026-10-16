// A method declaring `this: Ctx` read from a host that is no `Ctx`: its
// body would read `value` off an object without it, and `toFixed` of
// `undefined` throws.
class Ctx {
  value: number = 1;
}
class Holder {
  m(this: Ctx, digits: number): string {
    return this.value.toFixed(digits);
  }
}
export function wrongHost(h: Holder): string {
  // @ts-expect-error The 'this' context is not assignable to the method's 'this'
  return h.m(1);
}
