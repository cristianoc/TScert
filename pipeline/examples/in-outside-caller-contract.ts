// Under the caller contract, a value at a record type reads each stated
// optional field, own or inherited, as absent or a value of the field's
// type, and `k in v` finds the field only where it reads such a value. An
// error inherits `name` and `message` from `Error.prototype`, so an error at
// `{ name?: number }` or `{ message?: number }` is outside the contract: the
// functions verify, and under Node
// `withIn(Object.assign(new Error("m"), { size: 1 }))` returns "Error",
// `withMessage(Object.assign(new Error(), { size: 1 }))` returns "1" and
// `withoutIn(Object.assign(new Error(), { size: 1 }))` returns "1".
export function withIn(v: { name?: number; size: number }): number {
  return "name" in v ? (v.name ?? 0) : v.size;
}

export function withMessage(v: { message?: number; size: number }): number {
  return "message" in v && v.message !== undefined ? v.message + 1 : 0;
}

export function withoutIn(v: { message?: number; size: number }): number {
  return v.message !== undefined ? v.message + 1 : 0;
}
