// Bounds read at the arguments: a user alias's `K extends keyof T`,
// `Record`'s `keyof any`, and `Extract`, which has none.
type Get<T, K extends keyof T> = T[K];
export function got(x: Get<{ a: number; b: string }, "a">): number {
  return x;
}
export function recorded(x: Record<"a", number>): number {
  return x.a;
}
export function extracted(x: Extract<"a" | "b", "a">): "a" {
  return x;
}
