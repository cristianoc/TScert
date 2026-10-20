// `f` takes strings and numbers where the closure is written, as its context
// says, and the closure calls it with a number. Method bivariance lets the
// object stand for a `Narrow`, whose callers pass a function of strings only:
// `narrow.run((s) => s.length)` returns `undefined` (run under Node), no
// number.
interface Wide {
  run(f: (x: string | number) => number): number;
}
interface Narrow {
  run(f: (x: string) => number): number;
}
const wide: Wide = { run: (f) => f(1) };
export const narrow: Narrow = wide;
