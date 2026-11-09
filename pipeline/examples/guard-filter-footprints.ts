// Guard filters keep their callback's footprint and copy selected values.
export function pure(xs: readonly (string | number)[]): Modifies<{}, string[]> {
  return xs.filter((x): x is string => typeof x === "string");
}

export function writing(
  xs: readonly (string | number)[],
  seen: Set<number>,
): Modifies<{ values: "any" }, string[]> {
  return xs.filter((x): x is string => {
    seen.add(1);
    return typeof x === "string";
  });
}

export function growing(
  xs: readonly (string | number)[],
  seen: number[],
): Modifies<{ values: "any"; stores: "grow" }, string[]> {
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
