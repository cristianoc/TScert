// An application whose argument is computed over a binder: in the generic
// body it has no term, though every use reads.
type B<T extends string> = T;
type G<T extends { readonly k: string }> = keyof { a: B<T["k"]> };
export function f(x: G<{ k: "a" }>): "a" {
  return x;
}
