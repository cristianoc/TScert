// A builder passed at a parameter whose function type states a fresh
// result: the arrow returns the array `slice` allocates, so it meets the
// type, and `build` may call it.
export function build(make: () => Fresh<number[]>): number {
  return make().length;
}

export function use(xs: readonly number[]): number {
  return build(() => xs.slice());
}
