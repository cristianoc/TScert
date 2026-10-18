// `Object.entries` of an object no dictionary type states reads its values
// by [[Get]], which may run an external getter: that overload states no
// heap preservation, so a `map` calling it may leave holes in its result,
// which a `number[]` does not hold.
interface Named {
  name: string;
}
export function counts(ns: Named[]): number[] {
  return ns.map((n) => Object.entries(n).length);
}
