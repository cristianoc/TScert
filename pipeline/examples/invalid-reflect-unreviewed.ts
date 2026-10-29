// `Reflect.getPrototypeOf`, a function of `Reflect` no entry reviews, which
// answers the prototype itself (`Array.prototype` among them): refused.
export function proto(record: { a: number }): object | null {
  return Reflect.getPrototypeOf(record);
}
