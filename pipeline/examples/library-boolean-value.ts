// `Boolean` read as a value, the callable `(value: unknown) => boolean`:
// passed to `filter`, `every` and `some`, which call it with an element, an
// index and the array, of which it converts the first alone; held in a
// constant and called; and called directly, of no argument too.
export function words(line: string): string[] {
  return line.split(" ").filter(Boolean);
}

export function allSet(flags: readonly boolean[]): boolean {
  return flags.every(Boolean);
}

export function anyObject(values: readonly (object | null)[]): boolean {
  return values.some(Boolean);
}

export function truthy(v: unknown): boolean {
  const test: (value: unknown) => boolean = Boolean;
  return test(v) && Boolean(v) && !Boolean();
}
