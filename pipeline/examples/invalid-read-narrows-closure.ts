// The read is in a closure no one calls: `wrong([])` returns `undefined`.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[]): Declaration {
  const d = list[0];
  const kind = (): string | undefined => d.kind;
  return kind === undefined ? d : d;
}
