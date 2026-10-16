// A generic closure without a result annotation returns what its body
// returns: `1`, at every type argument, is no identity. At `T := string` the
// field returns a number where a string is promised.
export function wrong(): string {
  // @ts-expect-error
  const o: { fn: <T>(v: T) => T } = { fn: <T>(v: T) => 1 };
  return o.fn("a");
}
