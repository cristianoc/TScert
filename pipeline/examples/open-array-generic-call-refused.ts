// `x instanceof Array` on `unknown` finds a built-in array, a
// `readonly unknown[]`: a generic call at a mutable `Array<A>` needs, as `A`,
// the contract of the array's own store, which no type of the graph names.
declare function size<A>(a: Array<A>): number;

export function sizeOf(x: unknown): number {
  if (x instanceof Array) {
    return size(x);
  }
  return 0;
}
