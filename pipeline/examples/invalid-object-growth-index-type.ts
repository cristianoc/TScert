// A key added to a dictionary of numbers holds a string: the copy is no
// dictionary of numbers.
export function grow(): { [k: string]: number } {
  const d: { [k: string]: number } = {};
  d.x = "s";
  return d;
}
