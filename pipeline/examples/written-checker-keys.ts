// Keys as TypeScript computes them: a union's common keys, a numeric
// `Record` key, and a template literal bound read at the arguments.
type G<T, K extends keyof T> = K;
type Prefixed<T extends string, K extends `x${T}`> = K;
export function common(x: G<{ a: number } | { a: string }, "a">): "a" {
  return x;
}
export function numeric(x: G<Record<0, number>, 0>): 0 {
  return x;
}
export function template(x: Prefixed<"a", "xa">): "xa" {
  return x;
}
