// A `let` whose closure passes the binding to `map` in its own body: the
// read is the cell, never a self entry, and the cell is rebound before the
// call to a function reading `map`'s index as its optional second
// parameter, which returns `undefined` where a string is promised.
type Term = { readonly k: string; readonly parts: readonly Term[] };

export function wrong(t: Term): string {
  let show = (u: Term): string => {
    const names = u.parts.map(show);
    for (const name of names) return name;
    return u.k;
  };
  const first = show;
  show = (u: Term, at?: { readonly name: string }): string =>
    at === undefined ? u.k : at.name;
  return first(t);
}
