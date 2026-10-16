// `x instanceof Array`, with `Array` the standard library's, is the same
// test as `Array.isArray(x)`: the arm where it holds keeps the array parts
// of the tested type, and the arm where it fails the rest.
function length(x: number[] | string): number {
  return x instanceof Array ? x.length : x.length;
}

function typedArrayIdentity(a: Array<number>): void {
  if (a instanceof Array) {
    a.push(3);
  }
}

function negated(x: [number, string] | number | null): number {
  if (!(x instanceof Array)) return x ?? 0;
  return x[0];
}
