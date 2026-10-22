// A recursive constant whose body binds its name again, a loop variable
// holding a function known only by its type, and passes that to `map`: the
// read is the loop variable, never the self entry, and a function of the
// type may read `map`'s index as a further parameter, returning `undefined`
// where a string is promised.
type Term = { readonly k: string; readonly parts: readonly Term[] };
type Show = (u: Term) => string;

export function wrong(t: Term, shows: readonly Show[]): string {
  const show = (u: Term): string => {
    for (const show of shows) for (const name of u.parts.map(show)) return name;
    return u.k;
  };
  return show(t);
}
