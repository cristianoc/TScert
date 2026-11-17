// An element of a `Float64Array` is any number, so its read at `SafeInt` is
// refused. Under Node, with `values[0]` holding `0.5`, `pick(values, [1, 2])`
// reads `xs[0.5]`, `undefined` at `number`.

/** @requires 0 <= i && i < values.length */
function element(values: Float64Array, i: SafeInt): SafeInt {
  return values[i]!;
}

/** @requires 0 <= i && i < xs.length */
function at(xs: number[], i: SafeInt): number {
  return xs[i]!;
}

export function pick(values: Float64Array, xs: number[]): number {
  if (values.length === 0) return 0;
  const i = element(values, 0);
  if (0 <= i && i < xs.length) return at(xs, i);
  return 0;
}
