// A global declaration adding a required `label` to the standard library's
// `Iterable`, which a source reads at its merged declarations.
declare global {
  interface Iterable<T, TReturn, TNext> {
    label(): string;
  }
}
export {};
