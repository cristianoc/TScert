export async function wrap<T>(value: T): Promise<Awaited<T>> {
  return await value;
}

type Box = { n: number };

export function openRecord(value: Box): Promise<Box> {
  return wrap<Box>(value);
}
