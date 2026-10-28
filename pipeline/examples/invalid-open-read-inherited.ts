// A key `Object.prototype` holds is no open read: the read stays the
// model's, whose object holds no `Object.prototype`, and is refused.
export function method(x: unknown): unknown {
  return typeof x === "object" && x !== null && "toString" in x
    ? x.toString
    : null;
}
