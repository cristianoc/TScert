// A module constant holding an arrow of one parameter, passed where `map`'s
// callback binds three: the arrow's own code discards the further actuals,
// so the constant is claimed where it is created at its signature extended
// by a rest of `unknown`, which meets the callback's. Its body is certified
// heap-preserving, so the result is dense.
const shout = (s: string): string => s.toUpperCase();

export function shouted(words: string[]): string[] {
  return words.map(shout);
}

// A function expression and an arrow of no parameter.
const quoted = function (s: string): string {
  return `"${s}"`;
};
const empty = (): string => "";

export function quotedAll(words: string[]): string[] {
  return words.map(quoted);
}

export function emptied(words: string[]): string[] {
  return words.map(empty);
}
