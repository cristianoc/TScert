// A function whose parameter is narrower than the element, widened through a
// method signature, which TypeScript compares bivariantly: `map` passes it
// every element, an `A` among them, and its `part.n` reads `undefined`.
type F = { k: "f"; n: number };
type A = { k: "a"; s: string };
type T = A | F;
interface Sizer {
  size(part: F): number;
}
interface WideSizer {
  size(part: T): number;
}

export function wrong(xs: T[], sizer: Sizer): number[] {
  const wide: WideSizer = sizer;
  return xs.map(wide.size);
}
