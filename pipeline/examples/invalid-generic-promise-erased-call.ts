export async function wrap<T>(value: T): Promise<Awaited<T>> {
  return await value;
}

type Box = { n: number };

export function erasedCall(value: Box): Promise<unknown> {
  return wrap<Box>(value);
}
