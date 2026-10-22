// The member read runs a getter that writes the local it is read from: past
// the read the local holds `undefined`, which `wrong()` returns.

type Declaration = { kind?: string; initializer?: string };

export function wrong(): Declaration {
  let d: Declaration | undefined = undefined;
  const reset: Declaration = {
    get kind(): string {
      d = undefined;
      return "";
    },
  };
  d = reset;
  d.kind;
  return d;
}
