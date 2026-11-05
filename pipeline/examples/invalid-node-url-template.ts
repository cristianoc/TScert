// A template of a URL converts it by its `toString`, a member of the host's
// prototype the conversion contract does not cover: refused.
export function text(url: URL): string {
  return `${url}`;
}
