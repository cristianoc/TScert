// Defaults TypeScript computes at the arguments: a conditional, a template
// through an alias, `keyof` of a concrete default, `keyof` of a `Record`.
type Conditional<T, U = T extends string ? "yes" : "no"> = U;
type Prefix<T extends string> = `x${T}`;
type Prefixed<T extends string, U = Prefix<T>> = U;
type Numeric<T = { 0: number }, K extends keyof T = keyof T> = K;
type Recorded<T = Record<string, number>, K extends keyof T = keyof T> = K;
export function conditional(x: Conditional<"a">): "yes" {
  return x;
}
export function prefixed(x: Prefixed<"a">): "xa" {
  return x;
}
export function numeric(x: Numeric): 0 {
  return x;
}
export function recorded(x: "s"): Recorded {
  return x;
}
