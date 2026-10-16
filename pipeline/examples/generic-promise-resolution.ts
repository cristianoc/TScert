export async function wrap<T>(value: T): Promise<Awaited<T>> {
  return await value;
}

export async function forward<T>(value: T): Promise<Awaited<T>> {
  return value;
}

export async function stored<T>(value: T): Promise<Awaited<T>> {
  const observed = await value;
  return observed;
}

type Native<T> = Promise<T>;
type Result<T> = Awaited<T>;

export async function aliasWrap<T>(value: T): Native<Result<T>> {
  return await value;
}

export function numeric(value: number): Promise<number> {
  return wrap<number>(value);
}

export function array<T>(value: readonly T[]): Promise<readonly T[]> {
  return wrap<readonly T[]>(value);
}

export function native(value: Promise<number>): Promise<number> {
  return wrap<Promise<number>>(value);
}

export function nested(value: Promise<Promise<number>>): Promise<number> {
  return wrap<Promise<Promise<number>>>(value);
}

export function union(
  value: number | Promise<readonly string[]>,
): Promise<number | readonly string[]> {
  return wrap<number | Promise<readonly string[]>>(value);
}

export async function repeated<T>(value: T): Promise<Awaited<T>> {
  const result = await wrap<T>(value);
  return result;
}
