// A closure captures an alias before its initialization and retains it
// after the block. Adding x through another view makes its string read a number.
export function stale(): string {
  const o = {};
  const w: { x?: number } = o;
  let read: () => string | undefined = () => undefined;
  {
    const f = (): string | undefined => a.x;
    const a: { x?: string } = o;
    read = f;
  }
  w.x = 1;
  const value = read();
  return value === undefined ? "" : value.toUpperCase();
}
