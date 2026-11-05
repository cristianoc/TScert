// A subclass of `Uint8Array` is the constructor `subarray` constructs its
// result with (TypedArraySpeciesCreate), running the subclass's code, which
// replaces a string the caller narrowed (run under Node: a number): the
// global `Uint8Array` is only constructed, refused.
let label: string | number = "text";
class Counting extends Uint8Array {
  constructor(length: number) {
    super(length);
    label = 1;
  }
}
export function reset(): Uint8Array {
  const view = new Counting(4);
  label = "text";
  return view;
}
export function trimmed(view: Uint8Array): string {
  if (typeof label !== "string") return "";
  view.subarray(0, 1);
  return label;
}
