// The message is not enumerable: a spread does not copy it (run under Node:
// the copy's `message` is `undefined`), though TypeScript types the copy with
// it.
class Decline extends Error {}
function copy(): { message: string } {
  return { ...new Decline("x") };
}
export function main(): string {
  return copy().message;
}
