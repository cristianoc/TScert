// Awaiting a `PromiseLike` calls its `then`: JavaScript adopts a thenable,
// and the model awaits only a built-in promise or a primitive.
export async function settle(t: PromiseLike<number>): Promise<number> {
  return await t;
}
