// A subclass of `Float64Array` is the constructor `subarray` constructs its
// result with (TypedArraySpeciesCreate), running the subclass's code, which
// replaces a string the caller narrowed (run under Node: a number): the
// global `Float64Array` is only constructed, refused.
let label: string | number = "text";
class Counting extends Float64Array {
  constructor(length: number) {
    super(length);
    label = 1;
  }
}
export function reset(): Float64Array {
  const view = new Counting(4);
  label = "text";
  return view;
}
export function trimmed(view: Float64Array): string {
  if (typeof label !== "string") return "";
  view.subarray(0, 1);
  return label;
}
