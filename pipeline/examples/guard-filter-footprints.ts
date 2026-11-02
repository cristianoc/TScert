// Guard filters keep their callback's footprint and copy selected values.
export function pure(
  xs: readonly (string | number)[],
): Within<{ value: "keep"; store: "keep" }, string[]> {
  return xs.filter((x): x is string => typeof x === "string");
}

export function writing(
  xs: readonly (string | number)[],
  seen: Set<number>,
): Within<{ value: "any"; store: "keep" }, string[]> {
  return xs.filter((x): x is string => {
    seen.add(1);
    return typeof x === "string";
  });
}

export function growing(
  xs: readonly (string | number)[],
  seen: number[],
): Within<{ value: "any"; store: "grow" }, string[]> {
  return xs.filter((x): x is string => {
    seen.push(1);
    return typeof x === "string";
  });
}

export function shrinking(xs: (string | number)[]): string[] {
  return xs.filter((x): x is string => {
    xs.pop();
    return typeof x === "string";
  });
}
