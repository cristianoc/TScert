declare function wrap<T>(value: T): Promise<Awaited<T>>;
type Box = { n: number };

export function openRecord(value: Box): Promise<Box> {
  return wrap<Box>(value);
}
