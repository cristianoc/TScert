// `String` read as a value is the callable taking a primitive, converted
// without running code, and ignoring every further argument: `map` passes it
// each number with its index and the array, and stays dense; held in a
// constant and called, of a symbol too.
export function texts(xs: readonly number[]): string[] {
  return xs.map(String);
}

export function described(s: symbol, n: bigint | null): string {
  const show: (value: symbol | bigint | null | undefined) => string = String;
  return show(s) + show(n) + show(undefined) + String();
}
