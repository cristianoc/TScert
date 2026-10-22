// A write rebinds the local after the read: `wrong([{}])` returns the
// `undefined` the second element is.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[]): Declaration {
  let d = list[0];
  d.kind;
  d = list[1];
  return d;
}
