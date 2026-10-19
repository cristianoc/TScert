// `Object.hasOwn(e, "message")` observes ownness the stated instance does not
// carry: refused.
class Decline extends Error {}
export function own(): boolean {
  return Object.hasOwn(new Decline("x"), "message");
}
