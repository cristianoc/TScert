// A local `Object` is no global: its members are read and called as its type
// states, and no prototype test is recognized.
type Prototypes = { getPrototypeOf(o: object): number; prototype: number };
export function local(Object: Prototypes, o: object): boolean {
  return Object.getPrototypeOf(o) === Object.prototype;
}
