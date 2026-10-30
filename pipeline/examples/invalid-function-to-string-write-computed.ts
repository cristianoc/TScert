// A write at a computed key TypeScript types as the literal `"toString"` is
// a write of `toString`: on a function it gives the function an own one.
// The write is refused (SOURCE-CONTRACTS.md, "Function.prototype.toString").
const key: "toString" = "toString";
export function shadow(f: () => number, g: () => string): void {
  f[key] = g;
}
