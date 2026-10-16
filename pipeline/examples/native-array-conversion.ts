// Standard array conversion composes recursively, with no user conversion hooks.
export function tuples(values: [number, number][]): [number, number][] {
  return values.sort();
}

export function nested(
  values: readonly (readonly (readonly number[])[])[],
): string {
  return values.join("|");
}
