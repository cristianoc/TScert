// A mutable tuple may have grown past its positions (`push` is allowed on
// it): its position 1 is not `undefined`, as TypeScript reads it, but
// whatever was pushed.
export function second(
  source: [number] | [number, string],
): string | undefined {
  const [first, rest] = source;
  return rest;
}
