// A module constant annotated with a function type of one parameter: its
// value is known only by that type, which promises nothing of further
// actuals, and its code reads a second one. `map` passes the index there,
// whose `tag` is `undefined`, returned at `string`.
const tag: (s: string) => string = (s: string, o?: { tag: string }): string =>
  o === undefined ? s : o.tag;

export function tags(words: string[]): string[] {
  return words.map(tag);
}
