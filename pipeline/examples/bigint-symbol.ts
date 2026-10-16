// Bigints and symbols are bound, passed, stored and returned at their types,
// and members of unions like any other primitive.
export function keepBig(x: bigint): bigint {
  return x;
}
export function keepSymbol(s: symbol): symbol {
  return s;
}
export function either(x: bigint | symbol | null): bigint | symbol | null {
  const held: { value: bigint | symbol | null } = { value: x };
  return held.value;
}
