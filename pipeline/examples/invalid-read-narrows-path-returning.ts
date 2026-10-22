// A `fail` that returns: past `if (!d.initializer) warn(…)` the member may
// be absent, so `wrong([{}])` returns the `undefined` it reads where a
// string is returned (TypeScript also refuses it, TS2322).

type Declaration = { kind?: string; initializer?: string };

function warn(reason: string): void {
  void reason;
}

export function wrong(list: readonly Declaration[]): string {
  const d = list[0];
  if (d.kind) warn("an annotated declaration");
  if (!d.initializer) warn("a declaration needs an initializer");
  return d.initializer;
}
