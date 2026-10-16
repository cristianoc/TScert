interface Promise<T> {
  constructor: unknown;
}

async function read(p: Promise<{ n: number }>): Promise<number> {
  p.constructor = undefined;
  return (await p).n;
}
