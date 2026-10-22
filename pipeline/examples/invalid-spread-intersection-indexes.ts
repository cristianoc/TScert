// Two operands with index signatures: the copy's index would be their meet.
export function copied(x: { [k: string]: number } & { [k: string]: 1 | 2 }): {
  [k: string]: number;
} {
  return { ...x };
}
