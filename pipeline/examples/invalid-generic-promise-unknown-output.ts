type Box = { n: number };

export async function unknownOutput<T>(value: T): Promise<unknown> {
  return await value;
}

export function erasedOutputCall(value: Box): Promise<unknown> {
  return unknownOutput<Box>(value);
}
