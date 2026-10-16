// `Extract<T, U>` over a function's own type parameter is known only at an
// instance: TypeScript defers the conditional type.
export function pick<T>(x: Extract<T, string>): Extract<T, string> {
  return x;
}
