// An object with a callable `then` is no promise, and `await` calls its
// `then` instead of yielding it: it is not awaited at its own type, which
// only a primitive is.
type Thenable = { a: number; then(resolve: (v: string) => void): void };
export async function adopted(o: Thenable): Promise<number> {
  const x: Thenable = await o;
  return x.a;
}
