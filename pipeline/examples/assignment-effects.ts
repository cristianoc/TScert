// What an expression's assignments leave, and what writes keep.

// An assignment in each arm of a conditional expression.
function bothArms(flag: boolean): number {
  let state: number | undefined = undefined;
  const result = flag ? (state = 1) : (state = 2);
  return state + result;
}

// A computed key's assignment runs before the right side is read.
function keyThenRight(): number {
  let x: number | null = null;
  const box = { slot: 0 };
  box[(x = 1) === 1 ? "slot" : "slot"] = x;
  return box.slot;
}

// Writing an object into a cell keeps what is known of another object's
// fields: the cell was allocated apart from them.
function writeObject(
  x: { kind: "value"; f: number } | { kind: "empty" },
): number {
  let y: { readonly kind: "value"; readonly f: number } = {
    kind: "value",
    f: 0,
  };
  if (x.kind === "value") {
    y = x;
    const k: "value" = x.kind;
    x.f = 2;
  }
  return y.f;
}

declare function make(): { v: number };

// An object a call returned after the cell stands apart from nothing, and
// needs nothing to.
function newerCall(): number {
  let n: number = 0;
  const o = make();
  n = o.v;
  return n;
}
