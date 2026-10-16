// A `typeof` test naming a primitive family, on a value of a type parameter,
// narrows it to that family where it holds, as on `unknown`: TypeScript's
// `T & number` is a `number`.
export function onlyNumber<T extends number | string>(x: T): number {
  if (typeof x === "number") {
    return x;
  }
  return 0;
}

export function onlyString<T>(x: T): string {
  if (typeof x === "string") {
    return x;
  }
  return "";
}
