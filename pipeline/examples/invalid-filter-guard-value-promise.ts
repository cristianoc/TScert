// A guard passed by name to `filter` whose body does not establish its
// promise: `x !== undefined` holds of `null`, which `filter` would keep at
// `string[]`. Refused at the guard's return.
function isString(x: string | null): x is string {
  return x !== undefined;
}

export function strings(xs: (string | null)[]): string[] {
  return xs.filter(isString);
}
