// The read's throw is caught: past the `try`, `d` may be `undefined`, which
// `wrong([])` returns.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[]): Declaration {
  const d = list[0];
  try {
    d.kind;
  } catch {
    // the TypeError of reading a member of `undefined`
  }
  return d;
}
