// A member whose host must meet `Ctx` is no member callable on any host:
// TypeScript lets a method with a `this` parameter meet one without, and the
// call on a `Holder` then reads `value` off an object without it.
class Ctx {
  value: number = 1;
}
class Holder {
  m(this: Ctx, digits: number): string {
    return this.value.toFixed(digits);
  }
}
export function widened(h: Holder): string {
  const o: { m(digits: number): string } = h;
  return o.m(1);
}
