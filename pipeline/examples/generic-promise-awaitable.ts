// `T extends Awaitable` declares the observation-only qualification: `await`
// on `T` yields its observation, and a call takes an observable instance,
// a native promise of an open record included.
type Box = { n: number };

export async function log<T extends Awaitable>(value: T): Promise<void> {
  const observed = await value;
  observed;
}

export function record(value: Promise<Box>): Promise<void> {
  return log(value);
}

export function numeric(value: number): Promise<void> {
  return log(value);
}

export function native(value: Promise<number>): Promise<void> {
  return log(value);
}

export function union(value: number | Promise<Box>): Promise<void> {
  return log(value);
}
