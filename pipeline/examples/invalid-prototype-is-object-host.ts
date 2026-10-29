// `Object.getPrototypeOf(o) === Object.prototype` of a value typed `object`,
// which may be a host object, whose [[GetPrototypeOf]] may be the host's own
// code. Refused at the argument.
export function plain(value: unknown): boolean {
  return typeof value === "object" && value !== null && Object.getPrototypeOf(value) === Object.prototype;
}
