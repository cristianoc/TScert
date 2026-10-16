// The evolved contract is every write's: the closure reads `v` after the
// string is assigned, so it may return a string.
export function wrong(): number {
  let v = null;
  const read = (): number => (v === null ? 0 : v);
  v = "s";
  return read();
}
