// A URL's members are getters of `URL.prototype`, which a spread does not
// copy (run under Node: the copy's `href` is `undefined`): the copy of a
// host object states no member, refused.
export function copied(url: URL): string {
  return { ...url }.href;
}
