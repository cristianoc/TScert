// `map` callbacks building objects with spreads: a merge reads its sources'
// own properties and allocates their copy, which changes no location, so
// each callback is within `{value: any, store: keep}` and the results are
// dense.
type Binder = { name: string; bound: number | null };
export function bounded(binders: Binder[]): Binder[] {
  return binders.map((b) => ({ ...b, bound: 1 }));
}
export function renamed(binders: Binder[], prefix: string): Binder[] {
  return binders.map((b) => ({ ...b, name: prefix + b.name }));
}
