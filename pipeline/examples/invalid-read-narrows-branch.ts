// The read runs on one branch only: `wrong([], false)` returns `undefined`.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[], read: boolean): Declaration {
  const d = list[0];
  if (read) d.kind;
  return d;
}
