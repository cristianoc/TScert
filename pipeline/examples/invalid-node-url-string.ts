// `String` of a URL converts it by its `toString`: `String` is stated at
// the primitives, refused.
export function text(url: URL): string {
  return String(url);
}
