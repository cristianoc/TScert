// A member of a URL the overlay does not state, `pathname` (run under Node:
// a string, `/x` of `file:///x?q`): refused.
export function pathnameOf(url: URL): string {
  return url.pathname;
}
