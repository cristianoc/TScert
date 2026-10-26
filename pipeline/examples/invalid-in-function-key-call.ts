// A test that drops no function arm leaves `call` refused: `typeof x !==
// "number"` keeps the arrow, which inherits `call` from `Function.prototype`.
// Under Node, `report(() => 0)` returns true where the model's own-key test
// would answer false.
export function report(x: number | { size: number } | (() => number)): boolean {
  return typeof x !== "number" && "call" in x;
}
