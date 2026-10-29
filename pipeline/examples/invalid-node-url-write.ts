// A URL's `href` is a setter too, which parses again and changes its other
// members (run under Node: `moved()` is `http://example.com/a`): no member
// of a URL is written, refused.
export function moved(): string {
  const url = new URL("file:///x");
  url.href = "http://example.com/a";
  return url.href;
}
