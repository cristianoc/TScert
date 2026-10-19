// An object with a callable `then`, awaited at `{ a: number }`: the record
// type states no `then`, so it admits one, and JavaScript calls it (run under
// Node: the await settles to 42, not the object). The await is refused.
export async function widened(): Promise<unknown> {
  const thenable = {
    a: 1,
    then(resolve: (value: number) => void): void {
      resolve(42);
    },
  };
  const record: { a: number } = thenable;
  return await record;
}
