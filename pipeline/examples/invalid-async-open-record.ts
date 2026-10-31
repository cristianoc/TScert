// An open record can own or inherit a callable then, which async return adopts.
export async function wrap(o: { a: number }): Promise<{ a: number }> {
  return o;
}
