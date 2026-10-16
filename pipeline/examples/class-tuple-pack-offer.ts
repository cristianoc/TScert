// A class passed where an exact-tuple-pack construct signature is expected:
// its fixed signature covers the pack, whose lists are exactly the tuple's.
class Item {
  n: number;
  label: string;
  constructor(n: number, label: string) {
    this.n = n;
    this.label = label;
  }
}
function build(ctor: new (...params: [number, string]) => Item): number {
  return new ctor(2, "ab").n + new ctor(3, "c").label.length;
}
export const built = build(Item);
