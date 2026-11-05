// `new Intl.Segmenter` reads its options' `granularity` by [[Get]], which
// runs a getter there, here replacing a string the caller narrowed (run
// under Node: a number): an object literal's getter is refused.
let label: string | number = "text";
export function segmented(): string {
  if (typeof label !== "string") return "";
  const options = {
    get granularity(): "word" {
      label = 1;
      return "word";
    },
  };
  new Intl.Segmenter(undefined, options);
  return label;
}
