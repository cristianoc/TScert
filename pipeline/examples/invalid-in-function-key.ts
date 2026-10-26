// A function owns `name` and inherits `call` from `Function.prototype`, keys
// the model's function lacks: `in` with such a key is refused on an operand
// that may be a function, as an arrow arm makes it. Under Node,
// `report(() => 0)` returns true where the model's own-key test would answer
// false.
export function report(x: { size: number } | (() => number)): boolean {
  return "name" in x;
}
