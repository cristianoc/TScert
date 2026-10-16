// A symbol-keyed write is checked against the field's contract as a named
// write is: `o` is also a view whose `[tag]` holds only 1, which TypeScript
// lets the wider type alias.
const tag: unique symbol = Symbol("tag");
function write(o: { [tag]: number }): void {
  o[tag] = 5;
}
export function use(o: { [tag]: 1 }): 1 {
  write(o);
  return o[tag];
}
