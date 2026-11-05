// A subclass of `Intl.Segmenter` may replace `segment`, whose code then
// runs where a segmenter's `segment` is called, here replacing a string the
// caller narrowed (run under Node: a number): extending `Intl.Segmenter` is
// refused.
let label: string | number = "text";
class Counting extends Intl.Segmenter {
  segment(input: string): Intl.Segments {
    label = 1;
    return super.segment(input);
  }
}
export function make(): Intl.Segmenter {
  return new Counting(undefined, { granularity: "word" });
}
export function count(segmenter: Intl.Segmenter, text: string): string {
  if (typeof label !== "string") return "";
  segmenter.segment(text);
  return label;
}
