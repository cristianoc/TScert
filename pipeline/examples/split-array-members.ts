// A string's `split` gives an array, whose members are read from the array
// prototype: the source names no array type of its own.
export function joined(text: string): string {
  return text.split(",").join(";");
}
