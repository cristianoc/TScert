// A recursive constant passing its self entry to `find` in its own body
// while shrinking the iterated array: the closure's footprint is not the
// empty one, so `find`'s callback is its unrestricted one, its element
// `Term | undefined`, and a later visit hands the closure `undefined`,
// which it records as a `Term`.
type Term = { readonly k: string };

export function wrong(list: Term[]): Term[] {
  const seen: Term[] = [];
  const visit = (u: Term): boolean => {
    seen.push(u);
    list.pop();
    if (list.length > 0) list.find(visit);
    return false;
  };
  list.some(visit);
  return seen;
}
