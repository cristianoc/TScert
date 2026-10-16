// `typeof` comparisons test a value's shape, and refine an immutable
// binding on each arm.
export function widen(x: number | string | boolean | undefined): number {
  if (typeof x === "number") {
    return x;
  }
  return typeof x === "string" ? 1 : 0;
}
export function big(x: bigint | symbol | null): bigint | null {
  if (typeof x === "symbol") {
    return null;
  }
  return x;
}
export function call(f: ((x: boolean) => boolean) | null): boolean {
  if (typeof f !== "function") {
    return false;
  }
  return f(true);
}
// An intersection goes where its principal goes.
function tupleIntersection(
  x: ([number, string] & { length: 2 }) | number,
): number {
  if (typeof x === "number") {
    return x;
  } else {
    return x[0];
  }
}
