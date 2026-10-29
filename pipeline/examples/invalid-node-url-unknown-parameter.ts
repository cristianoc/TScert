// A URL passed at an `unknown` parameter may be given an own `href` (run
// under Node: a getter answering a number): no member of a URL is read,
// refused.
export function escaped(alias: (value: unknown) => void): string {
  const url = new URL("file:///tmp/x");
  alias(url);
  return url.href;
}
