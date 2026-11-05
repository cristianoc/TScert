// A program's object TypeScript accepts as an `Intl.Segmenter`, whose
// `segment` replaces a string the caller narrowed (run under Node: a
// number): the overlay's `Intl.Segmenter` is a host object's type, which no
// program object meets.
let label: string | number = "text";
export function fake(): Intl.Segmenter {
  return {
    segment(input) {
      label = 1;
      return new Intl.Segmenter(undefined, undefined).segment(input);
    },
    resolvedOptions() {
      return { locale: "en", granularity: "grapheme" };
    },
  };
}
export function count(segmenter: Intl.Segmenter, text: string): string {
  if (typeof label !== "string") return "";
  segmenter.segment(text);
  return label;
}
