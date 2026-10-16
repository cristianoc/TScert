// A function generic over a mutable `Array<A>` may rearrange the array it
// is given, which keeps every element an `A`. An array found in `unknown`
// may be a tuple, whose positions hold different types: no `A` is the
// contract of its store, and the rearranged tuple breaks its type.
function eachLen<A, B>(a: Array<A>, b: Array<B>): number {
  a.reverse();
  return a.length + b.length;
}

export function separateArrayParams(u: unknown, w: unknown): number {
  if (u instanceof Array && w instanceof Array) {
    return eachLen(u, w);
  }
  return 0;
}

export function caller(): string {
  const pair: [number, string] = [1, "s"];
  separateArrayParams(pair, []);
  return pair[0].toFixed();
}
