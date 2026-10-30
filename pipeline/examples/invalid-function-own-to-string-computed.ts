// A computed key TypeScript types as the literal `"toString"` is that key:
// `Object.assign` of an arrow and this literal gives the arrow its own
// `toString`, which a function's lookup finds before `Function.prototype`'s.
// The resolved key is refused (SOURCE-CONTRACTS.md,
// "Function.prototype.toString"). Under Node, `runs(f, "123")` calls the
// own `toString` and returns `true`.
const key: "toString" = "toString";
export const f = Object.assign<() => number, { toString: () => string }>(
  (): number => 0, { [key]: (): string => "123" });

export function runs(value: unknown, text: string): boolean {
  return typeof value === "function" && value.toString() === text;
}
