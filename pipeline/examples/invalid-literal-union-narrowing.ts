// Where either of two tests passed, the operand is either value, not the
// first one.
export function dense(value: unknown): "dense" | undefined {
  if (value === "dense" || value === "sparse") return value;
  return undefined;
}
