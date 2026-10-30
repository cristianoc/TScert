// A write of `toString` on a function gives the function an own `toString`,
// which its lookup then finds before `Function.prototype`'s. The write is
// refused (SOURCE-CONTRACTS.md, "Function.prototype.toString").
export function shadow(f: () => number, g: () => string): void {
  f.toString = g;
}
