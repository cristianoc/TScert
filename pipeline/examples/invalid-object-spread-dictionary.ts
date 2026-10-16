// A string field spread after a dictionary of numbers: the result's index
// holds a string too, so it is no dictionary of numbers.
export function view(a: { readonly [k: string]: number }): {
  readonly [k: string]: number;
} {
  return { ...a, x: "s" };
}
