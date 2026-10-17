// `&&` and `||` of strings, read for their truthiness in conditions and as
// values: a condition reads only the operands' truthiness, and a value is
// one operand's string.
export function both(s: string): number {
  if (s && s) return 1;
  return 0;
}

export function either(s: string, t: string): number {
  return s || t ? 1 : 0;
}

export function joined(s: string, t: string): string {
  return s && t;
}

export function fallback(s: string, t: string): string {
  return s || t;
}
