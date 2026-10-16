// A spread after a member replaces it with the source's: `copy.read` is
// `other.read`, a function the caller supplies, which may own a `call`
// property returning a string.
type Host = { value: number };
type Reader = { read: (this: Host) => number };

function overridden(other: Reader, source: Host): number {
  const copy = {
    read: function (this: Host): number {
      return this.value;
    },
    ...other,
  };
  return copy.read.call(source);
}
