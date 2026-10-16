// `typeof x === "object"` holds of null and of an object without call code;
// a callable object, a class included, is "function". `typeof x` as a value
// is the string naming the shape.
export function isObject(x: { a: number } | number | null): boolean {
  return typeof x === "object";
}
export function record(x: { a: number } | string): { a: number } {
  if (typeof x === "object") {
    return x;
  }
  return { a: 0 };
}
export function nullIsObject(x: null | string): string {
  if (typeof x === "object") {
    return "";
  }
  return x;
}
export function arrays(
  x: number[] | [number, string] | number,
  fallback: number[],
): number[] | [number, string] {
  if (typeof x !== "object") {
    return fallback;
  }
  return x;
}
export function functionIsNotObject(x: (() => number) | { a: number }): number {
  if (typeof x === "object") {
    return x.a;
  }
  return x();
}
export function name(
  x: number | string | boolean | null | undefined | (() => void),
): string {
  return typeof x;
}
export function sameShape(x: number | string, y: number | string): boolean {
  return typeof x === typeof y;
}
