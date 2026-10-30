// A default in an annotated pattern: the annotation gives `a` the type
// `number`, which the default `xs[0]` does not meet when `xs` is empty (run
// under Node: `f([])` returns true, `a` being `undefined`).
export function f(xs: number[]): boolean {
  const { a = xs[0] }: { a?: number } = {};
  return a === undefined;
}
