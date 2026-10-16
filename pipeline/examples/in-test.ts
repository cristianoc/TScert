// `"key" in o` asks whether `o` has the key, its own or an inherited one. A
// required field is owned, so the failed test drops its arm; an open record
// may own any other key, so the passed test keeps every arm that may.
export function required(x: { f: number }): boolean {
  return "f" in x;
}
export function optional(x: { f?: number }): number | undefined {
  if ("f" in x) {
    return x.f;
  }
  return 0;
}
export function either(x: { a: number } | { b: string }): string {
  if ("a" in x) {
    return "a";
  }
  return x.b;
}
export function arrays(xs: number[], f: () => number): boolean {
  return "extra" in xs && "extra" in f;
}
class Point {
  x: number = 0;
  norm(): number {
    return this.x;
  }
}
export function instance(p: Point): boolean {
  return "norm" in p;
}
// A key of a union of string singletons tests the one it holds.
export function eitherKey(s: "f" | "g", x: { f?: number; g: number }): boolean {
  return s in x;
}
export function afterTypeof(x: { a: number } | string): boolean {
  return typeof x === "string" ? false : "a" in x;
}
