// A type parameter typing a value and a rest is instantiated at the tuple of
// the actuals, which must be within its bound: a boolean is no `Safe`.
type Safe = string | number | object;
declare function inferTuple<Params extends readonly Safe[]>(
  ...args: Params
): Params;

export function wrong(): void {
  // @ts-expect-error: a boolean is no `Safe`
  inferTuple(true);
}
