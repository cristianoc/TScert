// The inner `then`'s rejection callback returns a number, which fixes
// `TResult2 := number` in place of its default `never`:
// `Promise<string | number>` is no `Promise<string>`.
export function show(p: Promise<number>): Promise<string> {
  // @ts-expect-error Type 'Promise<string | number>' is not assignable to type 'Promise<string>'
  return p.then((n: number) =>
    p.then(
      (m: number) => m.toString(),
      (e: unknown) => n,
    ),
  );
}
