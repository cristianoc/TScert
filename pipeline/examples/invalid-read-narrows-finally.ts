type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[]): Declaration {
  let d = list[0];
  try {
    d.kind;
  } finally {
    d = list[1];
  }
  return d;
}
