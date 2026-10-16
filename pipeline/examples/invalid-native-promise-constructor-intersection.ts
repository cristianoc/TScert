function clearConstructor(p: { constructor: unknown }): void {
  p.constructor = undefined;
}

async function read(p: Promise<{ n: number }>): Promise<number> {
  const value = await p;
  return value.n;
}

export function modifyAndRead(
  p: Promise<{ n: number }> & { constructor: unknown },
): Promise<number> {
  clearConstructor(p);
  return read(p);
}
