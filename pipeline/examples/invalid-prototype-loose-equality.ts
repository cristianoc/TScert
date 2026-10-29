// A loose comparison of the prototype is no prototype test: the call is read
// only in `===` or `!==`. Refused at the call.
export function plain(value: { a: number }): boolean {
  return Object.getPrototypeOf(value) == Object.prototype;
}
