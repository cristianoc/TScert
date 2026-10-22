// The read is the right operand of `&&`, skipped where `read` is false:
// `wrong([], false)` returns `undefined`.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[], read: boolean): Declaration {
  const d = list[0];
  read && d.kind;
  return d;
}
