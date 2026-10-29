// A declaration list whose later declarator reads an earlier pattern's
// binding at `string`: the pattern binds the array's first position, which
// an empty array does not hold (run under Node: `first([])` is undefined).
export function first(members: readonly string[]): Within<{ value: "any"; store: "grow" }, string> {
  const [member] = members, text: string = member;
  return text;
}
