// A write at `Symbol.toStringTag` is refused: an object holding the tag the
// native `Promise` contract requires of a prototype, beside `then`, `catch`
// and `finally`, passes for a promise's shape (run under Node:
// `Object.prototype.toString` reports `[object Promise]`), though no native
// operation takes it for one (`Promise.resolve` wraps it afresh).
export function forge(o: { [k: symbol]: string }): void {
  o[Symbol.toStringTag] = "Promise";
}
