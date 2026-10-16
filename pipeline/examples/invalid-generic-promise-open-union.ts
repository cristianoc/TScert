export async function wrap<T>(value: T): Promise<Awaited<T>> {
  return await value;
}

type Box = { n: number };

export function openUnion(value: number | Box): Promise<number | Box> {
  return wrap<number | Box>(value);
}
