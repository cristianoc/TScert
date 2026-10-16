// `keyof T` over a type parameter is known only at an instance.
export function key<T>(k: keyof T): keyof T {
  return k;
}
