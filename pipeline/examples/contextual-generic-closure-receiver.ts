// A function expression at a generic signature stating a receiver: the
// closure, its receiver written, takes the signature's type parameter R for
// its unannotated parameter.
interface Library {
  label: string;
  reviewed: <R>(this: Library, read: (text: string) => R) => R;
}
export function lengthOf(label: string): number {
  const library: Library = {
    label,
    reviewed: function (this: Library, read) {
      return read(this.label);
    },
  };
  return library.reviewed(t => t.length);
}
