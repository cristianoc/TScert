// A class value's copy holds its static fields; a construct signature states
// none and bounds none: a class with a static `a` holding a string overwrites
// the field written before it.
export function overStatic(k: new () => object): { a: number } {
  return { a: 1, ...k };
}
