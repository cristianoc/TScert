/**
 * A readonly field is a read capability: a view of a location whose stored
 * contract implies the stated bound. Reads through it observe the bound;
 * nothing writes through it; and another alias may still mutate the object,
 * whose invariant is never retyped by the view.
 */
/** A parameter whose field is only read. */
function readView(x: { readonly f: number }): number {
  return x.f;
}
/** A readonly view of a mutable object: the write through the other alias
 * is visible through the view, which promised only a number. */
function viewOfMutable(x: { f: number } | null): number {
  if (x !== null) {
    const y: { readonly f: number } = x;
    x.f = 2;
    return y.f;
  }
  return 0;
}
/** A mutable Boolean cell viewed as readonly Boolean. */
function viewOfFlag(x: { flag: boolean }): boolean {
  const view: { readonly flag: boolean } = x;
  x.flag = false;
  return view.flag;
}
/** `satisfies` a readonly view: the object keeps its own invariant. */
function satisfiesView(seed: number): number {
  const box = { value: seed };
  const first = box satisfies { readonly value: number };
  box.value = 2;
  return first.value;
}
