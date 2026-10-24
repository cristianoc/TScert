// A generic function declaration stating the empty footprint, called in a
// `map` callback at `number`: a unit reads a generic module function at its
// declared signature's instances, which keep no claimed footprint, so the
// callback is unrestricted and the result may hold holes.
function first<T>(
  xs: readonly T[],
  fallback: T,
): Within<{ value: "keep"; store: "keep" }, T> {
  const [x] = xs;
  return x === undefined ? fallback : x;
}

export function firsts(xss: number[][]): number[] {
  const r: number[] = xss.map((xs) => first(xs, 0));
  return r;
}
