// An optional field under a name `Object.prototype` holds: an object lacking
// it inherits the member, a function, where the type says a number or
// nothing.
export function optional(o: { toString?: number }): number {
  return o.toString ?? 0;
}
