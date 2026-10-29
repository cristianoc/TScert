// A function of `Reflect` read as a value, or by a computed key, is no call of
// the namespace's function: refused at the read.
export function extracted(record: { a: number }): (string | symbol)[] {
  const ownKeys = Reflect.ownKeys;
  return ownKeys(record);
}
