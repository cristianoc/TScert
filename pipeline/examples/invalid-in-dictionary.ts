// Where the test failed the key is absent: the read gives `undefined`.
export function absent(x: { [f: string]: number }): number {
  if (!("a" in x)) {
    return x.a;
  }
  return 0;
}
