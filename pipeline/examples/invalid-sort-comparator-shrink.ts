// A function stating {value: any, store: grow} that sorts with a comparator
// popping another array: the comparator changes a store beyond `grow`, so
// `sort` at it states no footprint and the statement is not established. A
// `map` calling the function would leave a hole in its result.
function sorted(
  values: number[],
  other: number[],
): Within<{ value: "any"; store: "grow" }, number[]> {
  return values.sort((a, b) => {
    other.pop();
    return a - b;
  });
}

export function wrong(xs: number[]): number[] {
  return xs.map(() => sorted([2, 1], xs).length);
}
