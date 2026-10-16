// `T extends Resolvable` declares the qualification `Awaited<T>` implies:
// `await` and async return on `T` take its descriptor, and a call takes a
// classified instance.
export async function settle<T extends Resolvable>(
  value: T,
): Promise<Awaited<T>> {
  const observed = await value;
  return observed;
}

export async function settleUnknown<T extends Resolvable>(
  value: T,
): Promise<unknown> {
  return await value;
}

export function numeric(value: number): Promise<number> {
  return settle<number>(value);
}

export function native(value: Promise<number>): Promise<number> {
  return settle<Promise<number>>(value);
}

export function union(
  value: number | Promise<string>,
): Promise<number | string> {
  return settle<number | Promise<string>>(value);
}
