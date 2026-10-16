// `BigInt` of any number or string, as TypeScript's declaration admits: it
// returns a bigint, or throws (`BigInt(1.5)` a RangeError, `BigInt("1.5")` a
// SyntaxError), which is an outcome, not a wrong value.
function toBig(x: number): bigint {
  return BigInt(x);
}

function half(): bigint {
  return BigInt(1.5);
}

function parsed(s: string): bigint {
  return BigInt(s) + BigInt("1.5");
}
