// A program's object TypeScript accepts as an `Intl.Segments`, whose
// iterator replaces a string the caller narrowed (run under Node: a
// number): the overlay's `Intl.Segments` is a host object's type, which no
// program object meets, and its loop steps the host's segment iterator.
let label: string | number = "text";
export function fake(): Intl.Segments {
  const data: Intl.SegmentData[] = [{ segment: "a", index: 0, input: "a" }];
  return {
    containing() {
      return undefined;
    },
    [Symbol.iterator]() {
      label = 1;
      return data.values();
    },
  };
}
export function count(segments: Intl.Segments): string {
  if (typeof label !== "string") return "";
  for (const _ of segments) break;
  return label;
}
