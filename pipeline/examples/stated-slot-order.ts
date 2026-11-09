// A local's nested write in source order (SOURCE-ELABORATION.md, "Slot or
// cell"): `acc ??= [7]` rebinds the slot, and the later read of `acc` in the
// same call's arguments reads the value it wrote (run under Node: `order()`
// is 11).
function pair(a: number[], n: number): number {
  return a.length * 10 + n;
}

export function order(): number {
  let acc: number[] | null = null;
  return pair((acc ??= [7]), acc.length);
}
