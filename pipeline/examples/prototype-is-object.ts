// `Object.getPrototypeOf(o) === Object.prototype`, either side, and `!==`, of
// a value that is no host object: whether its prototype is the realm's
// `Object.prototype`, a Boolean that hands the program no prototype.
export function plain(value: { a: number }): boolean {
  return Object.getPrototypeOf(value) === Object.prototype;
}
export function other(value: { [key: string]: unknown }): boolean {
  return Object.prototype !== Object.getPrototypeOf(value);
}
