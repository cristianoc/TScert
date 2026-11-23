// The pattern of cristianoc/TScert#351: a local copy of a field loses its
// link to the field at a loop head, so a read through the copy inside the
// loop is refused. `paperAssume` is the prototype's unsafe assume: the
// prototype adds the fact its equality states where it is evaluated, and
// names the issue in its verdict; the ordinary verifier reads it as a call
// that changes nothing.
function paperAssume(fact: boolean, issue: string): Modifies<{}, void> {}

// Refused by both today; the fix of #351 should accept it.
export function sumVia(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) s += xs[i]!;
  return s;
}

// The same with the link assumed: accepted by the prototype, naming #351.
export function sumViaAssumed(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) {
    paperAssume(xs === h.xs, "#351"); // unsafe assume until #351: the pass drops the link at the loop head
    s += xs[i]!;
  }
  return s;
}

// Must stay refused: the body sets h.xs to a longer array, so the guard
// admits an index past the copy's end and xs[i] reads past it (unsafe).
export function sumViaWrites(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) {
    h.xs = [...xs, 0];
    s += xs[i]!;
  }
  return s;
}

function touch(h: { xs: number[] }): Modifies<{ values: "any" }, void> {
  h.xs = [];
}

// Must stay refused: the call may change h.xs, so the link does not survive
// it. (Safe, since the guard runs before the call: unprovable, not unsafe.)
export function sumViaCalls(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) {
    touch(h);
    s += xs[i]!;
  }
  return s;
}
