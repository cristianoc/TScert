// ReturnType of a guard's typeof is its Boolean, the union of literals
// TypeScript computes for the application.
function isName(x: unknown): x is string {
  return typeof x === "string";
}
export function tested(x: unknown): boolean {
  type Tested = ReturnType<typeof isName>;
  const result: Tested = isName(x);
  return result;
}
