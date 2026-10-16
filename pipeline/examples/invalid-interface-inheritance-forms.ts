// The inherited member is the aliased declaration's, a number, not a string.
interface NominalBase<T> {
  readonly v: T;
}
type AliasOfNominal = NominalBase<number>;
interface ViaNominal extends AliasOfNominal {
  readonly k: string;
}
export function viaNominal(i: ViaNominal): string {
  return i.v;
}
