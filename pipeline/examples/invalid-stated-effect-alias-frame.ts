// A frame a declaration reads at its parameter, `Cb<P> = (i: number) =>
// Modifies<P, void>`, is not read at the application: the literal argument
// `{ values: "keep"; spines: "keep" }` is refused where it is written, and a
// type parameter there states the frame changing every location
// (SOURCE-CONTRACTS.md, "Arguments without type meaning").
type Cb<P extends { values?: "keep" | "any"; spines?: "keep" | "any" }> = (i: number) => Modifies<P, void>;
export function keepAcross(xs: number[], cb: Cb<{ values: "keep"; spines: "keep" }>): number {
  if (xs.length === 0) return 0;
  cb(0);
  return xs[0]!;
}
