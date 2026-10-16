// The inner `then` has no expected type, and its callback fixes only
// `TResult1`: TypeScript fills `TResult2` from its default, `never`.
export function show(p: Promise<number>): Promise<string> {
  return p.then((n: number) => p.then((m: number) => m.toString()));
}
