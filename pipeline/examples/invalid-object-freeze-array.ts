// `Object.freeze` of an array literal: the model's element write never
// raises, as every array is writable, but a frozen array's does (run under
// Node: TypeError, "Cannot assign to read only property '0'"). Only an
// object literal of named fields is admitted.
function first(xs: number[], v: number): void {
  xs[0] = v;
}

export function f(v: number): void {
  first(Object.freeze([1, 2]) as number[], v);
}
