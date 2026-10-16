// Bigints: literals in every spelling, literal types, arithmetic within the
// family, division, remainder and exponentiation by a literal the operation cannot throw
// on, comparisons across the two numeric families, and `typeof` as a tag.
const big: bigint = 9007199254740993n;
const hex: 16n = 0x10n;
const negative: -5n = -5n;
function double(x: bigint): bigint {
  return x * 2n + 1n;
}
function difference(a: bigint, b: bigint): bigint {
  return a - b;
}
function halve(x: bigint): bigint {
  return x / 2n;
}
function lastDigit(x: bigint): bigint {
  return x % 10n;
}
function cube(x: bigint): bigint {
  return x ** 3n;
}
function opposite(x: bigint): bigint {
  return -x;
}
function complement(x: bigint): bigint {
  return ~x;
}
function below(a: bigint, b: number): boolean {
  return a < b;
}
function above(a: number, b: bigint): boolean {
  return a > b;
}
function describe(x: bigint | string): string {
  if (typeof x === "bigint") {
    return "big";
  }
  return x;
}
function largest(): bigint {
  return big + hex + negative;
}
