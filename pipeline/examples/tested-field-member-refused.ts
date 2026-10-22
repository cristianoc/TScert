// A field a test narrowed, read again as a receiver in the test's right
// operand: past `k.name === "a"`, `k.name` holds "a".
type Name = { name: "a" | "b" | "c" | "d" };

export function single(k: Name): "a" | "x" {
  if (k.name === "a" && k.name.length === 1) return k.name;
  return "x";
}
