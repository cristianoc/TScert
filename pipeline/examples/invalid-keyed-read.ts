// `x[s]` reads `g` when `s` is "g": a string, not a number.
function pick(s: "f" | "g", x: { f: number; g: string }): number {
  const v: number | string = x[s];
  const n: number = x[s];
  return n;
}
