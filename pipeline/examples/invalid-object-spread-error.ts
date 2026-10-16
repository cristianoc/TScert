// An `Error`'s `message` is its own property, but not an enumerable one: a
// spread does not copy it, so the copy's `message` is `undefined`. TypeScript
// types the copy with it.
function copy(): { message: string } {
  return { ...new Error("boom") };
}
export function main(): string {
  return copy().message;
}
