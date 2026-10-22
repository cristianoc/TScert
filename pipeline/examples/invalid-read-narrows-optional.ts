// `d?.kind` reads no member where `d` is nullish: past it `d` may still be
// `undefined`, which `wrong([])` returns.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[]): Declaration {
  const d = list[0];
  d?.kind;
  return d;
}
