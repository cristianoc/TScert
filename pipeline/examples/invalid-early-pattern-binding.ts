// A pattern's binding a closure created before its declaration reads is
// outside the model's early bindings, which are one-name `let` and `const`:
// refused at the read.
export function first(xs: number[]): number {
  const get = (): number => a;
  const [a = 0] = xs;
  return get();
}
