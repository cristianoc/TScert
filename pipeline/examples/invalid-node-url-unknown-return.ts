// A URL returned at `unknown` reaches the caller, which may give it an own
// `href` before the program reads it again (run under Node: a getter
// answering a number): no member of a URL is read, refused.
export function make(): { url: URL; leaked: unknown } {
  const url = new URL("file:///tmp/x");
  return { url, leaked: url };
}

export function read(made: { url: URL }): string {
  return made.url.href;
}
