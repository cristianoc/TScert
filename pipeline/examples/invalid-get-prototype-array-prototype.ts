// `Object.getPrototypeOf([])` is `Array.prototype`: an array, so
// `Array.isArray` holds, outside `Array`'s chain, so `instanceof Array` does
// not. Under Node the push writes `Array.prototype[0]`, which every array's
// holes then read. Refused at the call.
export function f(): number {
  const p: object | null = Object.getPrototypeOf([]);
  if (p !== null && Array.isArray(p) && !(p instanceof Array)) {
    const xs: number[] = p;
    xs.push(1);
    return xs.length;
  }
  return 0;
}
