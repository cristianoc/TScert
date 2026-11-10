// A region through a mutable field is refused at `step`'s entry
// (FOOTPRINTS.md, "Fresh array storage"). `drain` replaces its fresh
// field with the caller's array inside `try`; `fail` throws, and `step`
// runs after the catch. The forged-table control selects `drain` alone
// to exercise freshness transport through this handler.
// Under Node, `console.log(total([1, 2, 3]))` prints `NaN`: the loop reads
// past the end of the array the calls shorten.
type Box = { open: number[] };

function step(box: Box): Modifies<{ values: "any"; stores: "grow"; "box.open[*]": "any" }, void> {
  box.open.pop();
}

function fail(): number {
  throw new Error("fail");
}

function drain(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, void> {
  const box: Box = { open: [] };
  try {
    box.open = xs;
    fail();
  } catch {
    // Continue to the regional call with the replaced field.
  }
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
