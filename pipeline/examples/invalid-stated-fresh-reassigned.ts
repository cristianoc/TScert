// A region through a mutable field is refused at the callee's entry
// (FOOTPRINTS.md, "Fresh array storage"): `step` names `box.open[*]`,
// but `open` is not `@stable`. This case exercises the entry restriction.
// `drain` replaces its fresh array with the caller's `xs` before `step`.
// Under Node, `console.log(total([1, 2, 3]))` prints `NaN`: the loop reads
// past the end of the array the calls shorten.
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
