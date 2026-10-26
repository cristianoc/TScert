// `Error.prototype` holds `message`, `""`, which an error built without a
// message does not own and the model does not hold: `"message" in v` is
// refused whatever the operand's type. Under Node,
// `wrong(Object.assign(new Error(), { size: 1 }))` returns the string "1".
export function wrong(v: { message?: number; size: number }): number {
  return "message" in v && v.message !== undefined ? v.message + 1 : 0;
}
