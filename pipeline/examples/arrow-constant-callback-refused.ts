// A module constant holding an arrow of one parameter, passed where `map`'s
// callback binds three: the arrow's own code discards the further actuals,
// as a module function's does, but only a module function is known to.
const shout = (s: string): string => s.toUpperCase();

export function shouted(words: string[]): string[] {
  return words.map(shout);
}
