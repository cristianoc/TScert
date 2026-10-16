// A closure created before the write holds the object: the write that would
// add a key is refused.
export function grow(): number {
  const o = { a: 1 };
  const read = (): number => o.a;
  o.b = 2;
  return read();
}
