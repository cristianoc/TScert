// `in` throws a TypeError on a primitive, where the model's test would
// answer `false`: the operand must be of object types. After these tests an
// `unknown` is still `unknown` here: no type names every object.
export function anything(x: unknown): boolean {
  return typeof x === "object" && x !== null && "a" in x;
}
