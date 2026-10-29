// A URL-valued base can invoke lazy search-parameter serialization hooks.
export function relative(base: URL): URL {
  return new URL("x", base);
}
