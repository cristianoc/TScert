// Awaiting a Promise<number> yields a number, not a string.
export async function wrong(p: Promise<number>): Promise<string> {
  const s: string = await p;
  return s;
}
