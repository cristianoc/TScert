// A loop head's binding exists, uninitialized, while the head's expression
// runs, and shadows the parameter of its name there: `for (const xs of xs)`
// throws a ReferenceError (run under Node), refused at the read.
export function total(xs: number[]): number {
  let n = 0;
  // @ts-expect-error: the head reads the binding it declares
  for (const xs of xs) n += xs;
  return n;
}
