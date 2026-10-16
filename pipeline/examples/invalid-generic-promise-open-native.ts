export async function wrap<T>(value: T): Promise<Awaited<T>> {
  return await value;
}

type Box = { n: number };

export function openNative(value: Promise<Box>): Promise<Box> {
  return wrap<Promise<Box>>(value);
}
