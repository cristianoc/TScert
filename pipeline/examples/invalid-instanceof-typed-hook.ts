// `x instanceof c` passes `x` to the `[Symbol.hasInstance]` the type of `c`
// states, whose parameter it must meet.
export function hook(
  x: { other: number },
  ctor: { readonly [Symbol.hasInstance]: (x: { value: number }) => boolean },
): boolean {
  return x instanceof ctor;
}
