// A pattern over a non-array iterable steps its own iterator; the model
// reads positions of arrays only.
export function firstChar(s: string): string | undefined {
  const [c] = s;
  return c;
}
