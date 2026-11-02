// Array rests preserve existing locations. A fixed tuple saves the later
// positions before allocation; a slice uses the standard array iterator.
export function fixed(
  xs: readonly [number, number, string],
): Within<{ value: "keep"; store: "keep" }, number> {
  const [, ...tail] = xs;
  return tail.length;
}

export function defaults(
  xs: readonly (number | undefined)[],
): Within<{ value: "keep"; store: "keep" }, number> {
  const [first = 7, second = first, ...tail] = xs;
  return first + second + tail.length;
}

export function nested(xs: {
  items?: readonly number[];
}): Within<{ value: "keep"; store: "keep" }, number> {
  const { items: [first = 0, ...tail] = [] } = xs;
  return first + tail.length;
}

export function inferred(xs: readonly number[]): number[] {
  return xs.map(() => {
    const [, ...tail] = xs;
    return tail.length;
  });
}

export function assigned(
  xs: readonly [number, number],
): Within<{ value: "any"; store: "keep" }, number> {
  let first: number | undefined = 0;
  let tail: [number] = [0];
  [first, ...tail] = xs;
  return tail.length;
}

export function parameter([first, ...tail]: readonly number[]): Within<
  { value: "keep"; store: "keep" },
  number
> {
  return tail.length;
}

export function fresh(
  xs: readonly number[],
): Within<{ value: "any"; store: "grow" }, number> {
  const [...tail] = xs;
  tail.pop();
  return tail.length;
}

export function copy(
  xs: readonly { value: number }[],
): Within<{ value: "keep"; store: "keep" }, { value: number }[]> {
  const [...tail] = xs;
  return tail;
}
