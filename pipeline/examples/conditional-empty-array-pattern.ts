// An array pattern, a spread and a loop over a conditional with an empty
// array literal in one arm: TypeScript types the literal as an empty tuple
// where a destructuring is its context, and `[] as const` as one anywhere, a
// type the compiler's API cannot write into the union's parts, so the
// iteration is read from each arm, the literal's being an array's. The other
// arm is a readonly array, as a node list's arguments are read.
export function firstArgument(args: readonly string[], call: boolean): string {
  const [operand] = call ? args : [];
  return operand ?? "";
}

export function copied(args: readonly number[], call: boolean): number[] {
  return [...(call ? args : [])];
}

export function firstLength(args: readonly string[], call: boolean): number {
  for (const arg of call ? args : ([] as const)) return arg.length;
  return 0;
}

export function main(): number {
  return firstArgument(["a"], true).length + firstArgument(["a"], false).length + copied([1, 2], true).length +
    firstLength(["ab"], true);
}
