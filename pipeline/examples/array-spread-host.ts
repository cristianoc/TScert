// `[...e]` over a string, a `Set`, a `Map` or a host collection iterator is
// `%Spread:K%(e)`: the fresh array of what the host's iterator yields.
export function f(s: Set<number>, t: string, m: Map<string, number>): number {
  const a: number[] = [...s];
  const b: string[] = [...t];
  const c: [string, number][] = [...m];
  return a.length + b.length + c.length;
}
