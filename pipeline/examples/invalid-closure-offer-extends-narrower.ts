// A function over an interface extending the element's, widened through a
// method signature, which TypeScript compares bivariantly: `map` hands it a
// `Base` without `size`, and its `size` reads `undefined` into the
// `number[]`.
interface Base {
  readonly label: string;
}
interface Sized extends Base {
  readonly size: number;
}
interface Measure {
  of(b: Sized): number;
}
interface WideMeasure {
  of(b: Base): number;
}

export function wrong(xs: Base[], measure: Measure): number[] {
  const wide: WideMeasure = measure;
  return xs.map(wide.of);
}
