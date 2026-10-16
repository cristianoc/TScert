// A trusted generic signature returning `Promise<T>`, at a `T` no thenable
// inhabits: a primitive, an array.
declare function wrap<T>(x: T): Promise<T>;
export async function wrapped(): Promise<number> {
  const n: number = await wrap(1);
  const xs: number[] = await wrap([n]);
  return xs.length;
}
