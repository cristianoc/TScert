// The right operand of `&&` sees the left operand's test, also where it
// reads members, calls a method or builds a regex before reading the tested
// parameter: a parameter holds one value throughout, so its read there has
// the type the test gave it on entry to the operand.
export function safeInteger(v: unknown): boolean {
  return typeof v === "number" && Number.isSafeInteger(v);
}
export function shorter(v: unknown, s: string): boolean {
  return typeof v === "number" && s.length > v;
}
export function digits(v: unknown): boolean {
  return typeof v === "string" && /^[0-9]+$/.test(v);
}
export function nonNegative(v: unknown): number {
  if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0)
    throw Error("expected a non-negative integer");
  return v;
}
// The test narrows nothing here: `v` stays `unknown`, as the method takes it.
export function untested(v: unknown, s: string): boolean {
  return s.length > 0 && Number.isSafeInteger(v);
}
