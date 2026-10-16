// `toString(radix)` throws a RangeError for a radix outside 2 to 36, and
// `toFixed`, `toExponential` and `toPrecision` for a digit count out of
// range: each returns a string or throws, whatever number it is given, as
// TypeScript's declarations admit.
function anyRadix(n: number, radix: number): string {
  return n.toString(radix);
}

function badRadix(n: number): string {
  return n.toString(1);
}

function digits(n: number, d: number): string {
  return n.toFixed(d) + n.toExponential(200) + n.toPrecision(0);
}

function bigRadix(b: bigint, radix: number): string {
  return b.toString(radix);
}
