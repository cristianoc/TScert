interface Ref<T> {
  contents: T;
}
export function overwrite<U, T extends Ref<U>>(x: T): U {
  // @ts-expect-error A number need not belong to U.
  x.contents = 1;
  return x.contents;
}
