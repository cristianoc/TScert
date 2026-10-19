// `Object.getPrototypeOf(e)` is `Decline.prototype`, which the stated
// instance reaches through its message link: refused.
class Decline extends Error {}
export function proto(): object | null {
  return Object.getPrototypeOf(new Decline("x"));
}
