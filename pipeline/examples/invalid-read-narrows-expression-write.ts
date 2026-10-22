type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[]): Declaration {
  let d = list[0];
  const k = (d.kind, (d = list[1]), 0);
  return d;
}
