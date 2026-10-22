// Operands of an intersection that state one member at different types:
// the member holds a value of both, `"a" | "b" | null`, which a truthiness
// test narrows to `"a" | "b"`.
type Param<T> = { name: string; bound: T | null };

export function both(
  binder: Param<string> & { bound: "a" | "b" | null },
): "a" | "b" | "none" {
  if (binder.bound) return binder.bound;
  return "none";
}
