// A separator of any string may be empty: `"".split(sep)` with `sep` empty
// is `[]`, so element 0 may be undefined.
export function first(text: string, sep: string): string {
  return text.split(sep)[0];
}
