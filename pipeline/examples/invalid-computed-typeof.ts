// `typeof` of a constant is its declared type, not its value.
const limit: number = 1;
export function bad(n: typeof limit): 1 {
  return n;
}
