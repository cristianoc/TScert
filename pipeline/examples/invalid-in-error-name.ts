// `Error.prototype` holds `name`, which the model does not hold, and any
// object, a record's value among them, may be an error: `"name" in v` is
// refused whatever the operand's type. Here a passed test would read an
// absent optional `name` as present at `number`; under Node,
// `wrong(Object.assign(new Error("m"), { size: 1 }))` returns "Error".
export function wrong(v: { name?: number; size: number }): number {
  return "name" in v ? (v.name ?? 0) : v.size;
}
