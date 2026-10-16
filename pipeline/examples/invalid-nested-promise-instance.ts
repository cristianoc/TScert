// A trusted generic signature states `Promise<T>` truthfully only at a `T`
// no thenable inhabits: at `T = Promise<number>`, the built-in promise `wrap`
// returns adopts its argument and fulfills with a number, never the
// `Promise<number>` its declaration states.
declare function wrap<T>(x: T): Promise<T>;
export async function nested(p: Promise<number>): Promise<number> {
  const q: Promise<number> = await wrap(p);
  return await q;
}
