// A key one operand of an intersection mentioning a type parameter states as
// a method and another as a data field: the meet is read at each instance
// as the model's, which would own the key, so the intersection is refused.
// `Object.assign(new Box(1), { tag: "t" })` is of the intersection, its
// `get` its prototype's; its copy has no `get` (run under Node).
class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  get(): T {
    return this.v;
  }
}
export function copied<T>(b: Box<T> & { get: () => T; tag: string }): {
  v: T;
  get: () => T;
  tag: string;
} {
  return { ...b };
}
