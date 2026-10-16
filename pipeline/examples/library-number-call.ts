// `Number` called on primitives through the reviewed overlay: it converts
// each without running client code, a symbol's TypeError an outcome.
function toNumber(
  v: string | boolean | bigint | null | undefined,
  s: symbol,
): number {
  return Number(v) + Number() + Number("0x1F") + Number(s);
}
