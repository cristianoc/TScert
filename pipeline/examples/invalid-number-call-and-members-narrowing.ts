// `Number` both called and read through its members keeps each method's
// contract: `Number.isSafeInteger(x)` is a Boolean that narrows nothing, so
// `x` stays a string or a number.
function wrong(x: string | number): number {
  return Number.isSafeInteger(x) ? x : Number(x);
}
