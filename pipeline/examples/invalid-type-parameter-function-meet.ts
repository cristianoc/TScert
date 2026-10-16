// Where `typeof x === "function"` holds, `x` is a function of no known
// signature: not one returning a number.
export function call<T>(x: T): () => number {
  if (typeof x === "function") {
    // @ts-expect-error Type 'T & Function' is not assignable to type '() => number'.
    return x;
  }
  return () => 0;
}
