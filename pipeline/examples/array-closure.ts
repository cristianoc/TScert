// Array literals and element reads inside closures, as at the top level; a
// literal expected as an Iterable is a readonly array there too.
export function make(n: number): () => number[] {
  return (): number[] => [n, n];
}
export function second(pair: [number, string]): () => string {
  return (): string => pair[1];
}
export function pairs(key: string): (n: number) => Iterable<[string, number]> {
  return (n: number): Iterable<[string, number]> => [[key, n]];
}
