// A declaration list of several declarators, patterns among them, each
// bound in turn: a later initializer reads an earlier pattern's binding.
// Census functions:
// declaration-graph.mts#collectDeclarations.
export function firsts(
  members: readonly string[],
  owners: readonly number[],
): Within<{ value: "any"; store: "grow" }, string> {
  const [member] = members, [owner] = owners;
  const count = owners.length, { size } = { size: count + 1 }, [again = member] = [owner === undefined ? member : undefined];
  return `${member ?? ""}${owner ?? 0}${count}${size}${again ?? ""}`;
}

// A `let` list whose bindings are written: each declarator's bindings are
// cells, the later initializer reading the earlier pattern's.
export function sums(xs: readonly number[]): Within<{ value: "any"; store: "grow" }, number> {
  let [a = 0] = xs, b = a + 1, { c } = { c: b };
  a += b;
  b += c;
  c = a;
  return a + b + c;
}
