// A `let` holding its own object, which a closure captures after its last
// write, is a slot of its activation: a key-adding write rebinds the copy to
// the slot, checked at its contract, and to the constant bound to it.
export function grownSlot(
  key: string,
  reset: boolean,
): () => { [k: string]: number } {
  let obj: { [k: string]: number } = {};
  const ref = obj;
  obj[key] = 1;
  obj.count = 2;
  if (reset) {
    obj = {};
  }
  return () => (reset ? ref : obj);
}
