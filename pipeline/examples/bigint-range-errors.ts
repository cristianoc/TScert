// A bigint division or remainder by zero and a negative bigint exponent throw a
// RangeError. A throw is an outcome, not a wrong value: any divisor and any
// exponent are admitted, as TypeScript admits them.
function share(total: bigint, parts: bigint): bigint {
  return total / parts;
}

function leftover(total: bigint, parts: bigint): bigint {
  return total % parts;
}

function inverse(x: bigint): bigint {
  return x ** -1n;
}

function power(x: bigint, e: bigint): bigint {
  return x ** e;
}
