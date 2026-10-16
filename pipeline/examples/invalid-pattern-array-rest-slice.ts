// A slice holds what the arms hold from the rest's index on: from 0, the
// number at position 0 too.
export function fromStart(source: [number] | [number, string]): string[] {
  const [...all] = source;
  // @ts-expect-error A number is no string.
  return all;
}
