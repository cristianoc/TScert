// `Object.hasOwn(e, "message")` is `true` in JavaScript, where the model places
// the message on a link: a Boolean either way.
class Decline extends Error {}
export function own(): boolean {
  return Object.hasOwn(new Decline("x"), "message");
}
