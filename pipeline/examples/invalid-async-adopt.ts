// An async function adopts a returned promise: its own promise settles to a
// number, which the `string` its annotation states does not admit.
export async function forwards(p: Promise<number>): Promise<string> {
  return p;
}
