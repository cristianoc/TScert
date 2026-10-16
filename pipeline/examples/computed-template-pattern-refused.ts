// A template literal type with a `${string}` hole holds infinitely many
// strings: a pattern, which no type of the fragment states.
export function id(x: `id-${string}`): string {
  return x;
}
