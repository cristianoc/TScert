// The callback's contextual parameter is a mapped identity written over a
// named record, settled before the closure's parameter is read.
interface S {
  n: number;
}
export function use(
  f: (x: { readonly [P in keyof S]: S[P] }) => number,
): number {
  return f({ n: 1 });
}
export function run(): number {
  return use((x) => x.n);
}
