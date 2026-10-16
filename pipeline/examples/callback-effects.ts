// The native call consumes the inferred type of a returned or bound callback.
// Its body is checked at definition, before either use of Array.prototype.map.
export function returnedCallback(xs: number[]): number[] {
  const make =
    () =>
    (value: number, _index: number, _array: readonly number[]): number =>
      value + 1;
  const next = make();
  return xs.map(next);
}

export function boundCallback(xs: number[]): number[] {
  const next = (
    value: number,
    _index: number,
    _array: readonly number[],
  ): number => value + 1;
  const bound = next.bind(undefined);
  return xs.map(bound);
}

// A readonly read supplies a value contract; readonly alone is not the effect.
export function readCallback(xs: { readonly value: number }[]): number[] {
  return xs.map((x: { readonly value: number }) => x.value);
}

// The callback allocates new locations but leaves every input location intact.
export function allocatingCallback(xs: number[]): { values: number[] }[] {
  return xs.map((x) => ({ values: [x] }));
}

// The nested call uses its selected signature, including the omitted default.
export function callingCallback(xs: number[]): number[] {
  const add: (n: number, delta?: number) => number = (
    n: number,
    delta = 1,
  ): number => n + delta;
  return xs.map((n: number) => add(n));
}
