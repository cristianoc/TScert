// Standard library globals read through the reviewed overlay: `BigInt` of a
// bigint, a Boolean, an integer literal and a string literal it parses (any
// number or string is admitted too: `bigint-conversions`), `Symbol` and
// `String` as called, and `console.log` as output.
function toBig(x: bigint, flag: boolean): bigint {
  return (
    BigInt(x) +
    BigInt(flag) +
    BigInt(42) +
    BigInt(-7) +
    BigInt("0xFF") +
    BigInt("12345678901234567890")
  );
}

function fresh(): symbol {
  const described: symbol = Symbol("tag");
  const numbered: symbol = Symbol(3);
  return Symbol();
}

function show(v: number | boolean | symbol | bigint | undefined): string {
  console.log("showing", v);
  return String(v);
}
