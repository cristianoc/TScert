// `JSON.stringify` at a JSON value and `Error` at a string message run no
// code of the client's and write nothing they did not allocate: a callback
// calling them keeps `map`'s result dense.
function quoted(s: string): string {
  return JSON.stringify(s);
}
export function quotedAll(xs: string[]): string[] {
  return xs.map(quoted);
}
function checked(n: number): number {
  if (n < 0) throw Error(`negative: ${JSON.stringify(n)}`);
  return n;
}
export function checkedAll(xs: number[]): number[] {
  return xs.map(checked);
}
