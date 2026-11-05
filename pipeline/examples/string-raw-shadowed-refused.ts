// A tag named `String` that is a parameter, not the global: no overlay
// entry reads it, and a tagged template of another tag is refused.
export function tagged(String: { raw(template: unknown): string }): string {
  return String.raw`a`;
}
