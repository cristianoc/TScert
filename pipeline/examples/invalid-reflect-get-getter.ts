// `Reflect.get(o, k)` runs [[Get]], which calls an accessor's getter: code
// no type of `o` states (run under Node: the getter empties the array its
// caller holds). Refused at the call.
export function read(o: object): unknown {
  return Reflect.get(o, "x");
}
