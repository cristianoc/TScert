// An interface inherits through an alias of another declaration, and from
// two bases stating the same index signature.
interface NominalBase<T> {
  readonly v: T;
}
type AliasOfNominal = NominalBase<number>;
interface ViaNominal extends AliasOfNominal {
  readonly k: string;
}
export function viaNominal(i: ViaNominal): number {
  return i.v + i.k.length;
}

interface A {
  [key: string]: number;
}
interface B {
  [key: string]: number;
}
interface C extends A, B {}
export function indexed(): number | undefined {
  const c: C = { x: 1, y: 2 };
  return c.x;
}
