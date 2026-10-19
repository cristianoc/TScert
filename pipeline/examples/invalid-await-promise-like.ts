// `await` of a `PromiseLike`, a structural record with a callable `then`:
// neither a native promise nor stably non-thenable, so the await is refused;
// JavaScript calls the `then` (run under Node: a thenable passed settles to
// 42).
export async function awaited(x: PromiseLike<number>): Promise<number> {
  return await x;
}
