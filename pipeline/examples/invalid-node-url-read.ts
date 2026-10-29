// Even href's standard getter can serialize externally aliased search params.
export function hrefOf(url: URL): string {
  return url.href;
}
