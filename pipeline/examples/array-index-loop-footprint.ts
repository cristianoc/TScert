// An array walked by index within a stated `{value: any, store: grow}`, the
// form type-term.mts's `quantified` and `signatures` use where they read
// each element with its position (SOURCE-REWRITES.md, "An array's entries
// iterated by index"). `for (const [i, x] of xs.entries())` steps an
// `ArrayIterator`, which the overlay reads as a structural iterator of no
// stated effect.
type Binder = { name: string; bound: string | null };

export function bind(
  names: readonly string[],
  binders: Binder[],
  fail: (message: string) => never,
): Within<{ value: "any"; store: "grow" }, number> {
  for (let index = 0; index < names.length; index++) {
    const name = names[index];
    const binder = binders[index];
    if (name === undefined || !binder) return fail("missing type parameter");
    binder.bound = name.length ? name : null;
  }
  return binders.length;
}
