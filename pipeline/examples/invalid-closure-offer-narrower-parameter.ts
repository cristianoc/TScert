// A function whose parameter is narrower than the element, widened through a
// method signature, which TypeScript compares bivariantly: `map` passes it
// every element, an `A` among them, and its `part.n` reads `undefined`.
// On the single pass, a gap: the single pass refuses `wide.size`, a method
// read as a function value (a stated restriction), before the binding that
// narrows the parameter.
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
