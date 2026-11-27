// An explicitly open object parameter may carry extra properties of arbitrary
// types at runtime (for example `{ a: 1, extra: "boom" }`), so it cannot
// satisfy a readonly string index signature `{ readonly [k: string]: number }`.
function readExtra(d: { readonly [k: string]: number }): number {
  const v = d["extra"];
  return v !== undefined ? v : 0;
}

export function unsoundOpenToDict(p: {
  readonly inner: { a: number };
}): number {
  const ro: { readonly inner: { readonly [k: string]: number } } = p;
  return readExtra(ro.inner);
}
