// An instance method keyed by `Symbol.hasInstance` is an ordinary method:
// its call passes its actuals to its parameters, which they must meet.
class Matcher {
  a: number = 1;
  [Symbol.hasInstance](x: { value: number }): boolean {
    return x.value.toFixed(0) === "0";
  }
}

export function call(m: Matcher, x: { other: number }): boolean {
  // @ts-expect-error the actual lacks `value`
  return m[Symbol.hasInstance](x);
}
