// A computed key whose expression, a name or a member read, TypeScript types
// as one string or number literal is the key that literal spells: a `const`
// binding's string, an enum member's number by its `ToString`.
const awaitName = "%Await%";

enum Op {
  Neg = 1,
  Plus = 2,
}

export function names(): number {
  const table = { [awaitName]: 0, [Op.Neg]: "neg", [Op.Plus]: "plus" };
  return table[awaitName] + table[1].length + table["2"].length;
}
