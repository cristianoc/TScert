// The closure is created before the write: it reads the binding when it
// runs, after `x = undefined`, and returns undefined. The binding is a cell,
// read at its contract, which the cast does not narrow.
export function stale(): () => string {
  let x: string | undefined = "a";
  const f = (() => x) as () => string;
  x = undefined;
  return f;
}
