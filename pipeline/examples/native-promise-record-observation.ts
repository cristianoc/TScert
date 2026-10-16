export async function read(p: Promise<{ n: number }>): Promise<number> {
  const value = await p;
  return value.n;
}
export async function readAll(
  ps: Array<Promise<{ n: number }>>,
): Promise<number> {
  const values = await Promise.all(ps);
  const first = values[0];
  if (first === undefined) {
    return 0;
  } else {
    return first.n;
  }
}
export function gather(
  ps: Array<Promise<{ n: number }>>,
): Promise<Array<{ n: number }>> {
  return Promise.all(ps);
}
