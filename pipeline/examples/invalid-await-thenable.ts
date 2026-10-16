// A record may be a thenable, whose `then` an `await` would call instead of
// yielding the record: only a Promise is awaited.
export async function adopt(o: { a: number }): Promise<number> {
  const v: { a: number } = await o;
  return v.a;
}
