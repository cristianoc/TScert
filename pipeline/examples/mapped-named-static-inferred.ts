// A static field's inferred type is a mapped identity written over a named
// record, settled before the field's type is read.
interface Item {
  readonly value: number;
}
function make(): { readonly [P in keyof Item]: Item[P] } {
  return { value: 7 };
}
class Holder {
  static readonly item = make();
}
export function read(): number {
  return Holder.item.value;
}
