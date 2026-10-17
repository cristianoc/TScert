// An empty separator splits an empty string into no elements:
// `"".split("")` is `[]`, so element 0 may be undefined.
export function first(text: string): string {
  return text.split("")[0];
}
