// `Boolean` as a value states no promise about its argument, as its
// declaration states none: `filter(Boolean)` keeps the element type, and its
// result is no array of strings.
export function present(xs: readonly (string | undefined)[]): string[] {
  // @ts-expect-error TypeScript keeps the element type too
  return xs.filter(Boolean);
}
