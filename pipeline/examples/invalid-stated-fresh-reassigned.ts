// A field that is not `@stable`, reassigned before the call (FOOTPRINTS.md,
// "Fresh array storage"): `box.open` is allocated fresh, then assigned the
// caller's `xs`. A region read through a field that is not stable is refused
// at `step`'s entry, and the fresh field's fact is not carried across a node
// that may change the field, so `drain`'s `stores: "grow"` is refused at the
// call too. Run under Node, `total([1, 2, 3])` reads past the end of the
// array the calls empty and returns `NaN`.
type Box = { open: number[] };

function step(box: Box): Modifies<{ values: "any"; stores: "grow"; "box.open[*]": "any" }, void> {
  box.open.pop();
}

function drain(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, void> {
  const box: Box = { open: [] };
  box.open = xs;
  step(box);
}

export function total(xs: number[]): number {
  let sum = 0;
  for (let i = 0; i < xs.length; i++) {
    drain(xs);
    sum += xs[i]!;
  }
  return sum;
}
