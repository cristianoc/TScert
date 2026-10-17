// The empty literal is built at the other arm's type, an array of strings:
// its elements are no numbers.
export function lengths(text: string): number[] {
  const lines = text === "" ? [] : text.split("\n");
  return lines;
}
