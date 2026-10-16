// A grown local handed to a callee as a writable dictionary: the callee may
// add keys at the dictionary's type, so from the call on the local's object
// is claimed as a record, and a view that would say `x` is absent is not
// derived.
declare function add(d: { [k: string]: string }): void;
export function grow(): number | undefined {
  const o = {};
  o.y = "s";
  add(o);
  const b: { y: string; x?: number } = o;
  return b.x;
}
