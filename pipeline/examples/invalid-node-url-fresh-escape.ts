// A URL the program constructs and passes on may meet other code, which can
// give its search parameters a `toString` that its `href` getter then runs
// (run under Node). No member of a URL is read, refused.
export function escaped(alias: (url: URL) => void): string {
  const url = new URL("file:///tmp/x");
  alias(url);
  return url.href;
}
