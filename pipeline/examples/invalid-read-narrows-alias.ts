// The read is of a copy taken before the local was rebound: it narrows the
// copy, and `wrong([{}])` returns the `undefined` the local holds.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[]): Declaration {
  let d = list[0];
  const e = d;
  d = list[1];
  e.kind;
  return d;
}
