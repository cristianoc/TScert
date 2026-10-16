// `x instanceof c`, where the type of `c` states `[Symbol.hasInstance]`,
// reads that method off `c` and calls it with `x`,
// `c` its receiver, converting the result to a Boolean: nothing is narrowed.
// A class's static `[Symbol.hasInstance]` is an own property of the class
// value, so the class meets such a type.
class MembershipPlain {
  value: number = 0;
}
class MembershipNumeric {
  value: number = 0;
  static [Symbol.hasInstance](x: { value: number }): boolean {
    return x.value.toFixed(0) === "0";
  }
}
export function retained(x: { value: number }): boolean {
  const ctor: {
    new (): MembershipPlain;
    readonly [Symbol.hasInstance]: (x: { value: number }) => boolean;
  } = MembershipNumeric;
  return x instanceof ctor;
}
export function hook(
  x: { value: number },
  ctor: { readonly [Symbol.hasInstance]: (x: { value: number }) => boolean },
): number {
  return x instanceof ctor ? 1 : 0;
}
