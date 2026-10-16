// The rest of a tuple holds the positions after the elements, not the first.
export function restPositions(
  tuple: [number, string, boolean],
): [number, boolean] {
  const [first, ...rest] = tuple;
  return rest;
}
