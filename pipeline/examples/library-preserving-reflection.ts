// Callbacks reading an object's own keys, a dictionary's values and entries,
// testing a key known only at run time and converting a string to a bigint:
// none runs client code or writes a location it did not allocate, so each
// call states heap preservation and `map`'s result is dense.
type Dictionary = { [key: string]: number };
export function sizes(ds: Dictionary[]): number[] {
  return ds.map(
    (d) =>
      Object.keys(d).length +
      Object.values(d).length +
      Object.entries(d).length,
  );
}
export function present(ds: Dictionary[], key: string): boolean[] {
  return ds.map((d) => key in d);
}
export function large(ss: string[]): boolean[] {
  return ss.map((s) => /^[0-9]+$/.test(s) && BigInt(s) > 0xffffffffn);
}
