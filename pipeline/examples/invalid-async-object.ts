// An async function's promise settles to what it returns, unless that is a
// thenable, which JavaScript adopts instead: an object is not returned.
export async function wrap(o: { a: number }): Promise<{ a: number }> {
  return o;
}
