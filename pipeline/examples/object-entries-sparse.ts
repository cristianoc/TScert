// `Object.entries` of an object no dictionary type states reads its values
// by [[Get]], which may run an external getter: that overload states no heap
// preservation, so a `map` calling it is read at its unrestricted signature,
// whose result may hold holes.
interface Named {
  name: string;
}
export function counts(ns: Named[]): (number | undefined)[] {
  return ns.map((n) => Object.entries(n).length);
}
