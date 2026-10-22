// The values a method of a class instance computes, collected by a loop
// pushing onto a fresh array rather than by a `map` callback: `push` keeps
// the array dense whatever the method does, so the result is bound at an
// annotation without holes. The shape of `protocolPattern`'s bindings
// (`tools/fragment-statements.mts`).
type Binding = {
  early: boolean;
  name: string;
  annot: string | null;
  init: { k: "id"; name: string };
};

export class Names {
  prefix: string = "";
  local(n: string): string {
    return this.prefix + n;
  }
}

export function bindings(
  names: Names,
  named: { cell: string; name: string }[],
): Binding[] {
  const out: Binding[] = [];
  for (const { cell, name } of named)
    out.push({
      early: false,
      name: names.local(name),
      annot: null,
      init: { k: "id", name: cell },
    });
  return out;
}
