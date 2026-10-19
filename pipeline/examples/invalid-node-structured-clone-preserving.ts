// A JSON array may own an enumerable getter beside its elements, which
// `structuredClone` runs (run under Node: a getter popping the mapped array
// leaves a hole in the result): the call states no effect, so the `map`
// calling it is not known dense.
type Json =
  | null
  | boolean
  | number
  | string
  | readonly Json[]
  | { readonly [key: string]: Json };
export function rows(xs: number[], value: Json): number[] {
  return xs.map((x) => {
    structuredClone(value);
    return x;
  });
}
