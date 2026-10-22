type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[]): Declaration {
  let d = list[0];
  for (let i = 0; i < 1; i++) {
    d.kind;
    d = list[1];
  }
  return d;
}
