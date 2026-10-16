// A passed test against a string or a nonzero number leaves its operand that
// value alone, whatever it was before, `unknown` included; a disjunction of
// such tests leaves it one of their values, on the edge either operand took.
export type Presence = "dense" | "readable" | "sparse";

export function presence(value: unknown): Presence | undefined {
  if (value === "dense" || value === "readable" || value === "sparse")
    return value;
  return undefined;
}

export function presenceOf(value: string): Presence | undefined {
  return value === "dense" || value === "readable" || value === "sparse"
    ? value
    : undefined;
}

export function digit(value: unknown): 1 | 2 | "one" | null {
  return value === 1 || value === 2 || value === "one" ? value : null;
}

export function prefixed(value: unknown): string {
  if (!(value === "dense" || value === "sparse")) return "other";
  const p: "dense" | "sparse" = value;
  return p;
}
