// A destructured local reusing the name of an owned local from a block left
// before is a binding of its own, holding an object another reference holds:
// the write that would add the key is refused.
export function reusedName(): string {
  {
    const o = { c: 1 };
  }
  const p = { b: 1 };
  const view: { b: number; a?: string } = p;
  const xs: [{ b: number; a?: number }] = [p];
  {
    const [o] = xs;
    o.a = 1;
  }
  const v = view.a;
  return v === undefined ? "" : v.toUpperCase();
}
