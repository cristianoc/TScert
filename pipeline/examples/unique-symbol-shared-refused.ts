// `Symbol.for("k")` returns the registry's symbol for "k": two constants made
// so hold the same symbol, so a type naming both keys names one key twice,
// though TypeScript types each constant a distinct unique symbol.
const a: unique symbol = Symbol.for("k");
const b: unique symbol = Symbol.for("k");
export function read(o: { [a]: number; [b]: string }): number {
  return o[a];
}
