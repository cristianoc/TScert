// An unstated getter can remove an array element before its caller reads it.
// Under Node, read([1], an object whose getter pops that array) is undefined.
export function read(xs: number[], o: object): number {
  if (xs.length === 0) return 0;
  Reflect.get(o, "x");
  return xs[0];
}
