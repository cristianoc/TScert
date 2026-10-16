type StableRecord = { readonly tag: number; readonly then?: number };
type NumericWrapper = <T extends number>(value: T | Promise<T>) => Promise<T>;
type NumericUnknownWrapper = <T extends number>(
  value: T | Promise<T>,
) => Promise<unknown>;

export async function stable<T extends number>(value: T): Promise<T> {
  return value;
}

export async function stableUnknown<T extends number>(
  value: T,
): Promise<unknown> {
  return value;
}

export async function adoptUnknown<T extends number>(
  value: Promise<T>,
): Promise<unknown> {
  return value;
}

export async function wrap<T extends number>(
  value: T | Promise<T>,
): Promise<T> {
  return value;
}

export function fromNumber(value: number): Promise<number> {
  return wrap<number>(value);
}

export function fromNative(value: Promise<number>): Promise<number> {
  return wrap<number>(value);
}

export function widenResult(wrapper: NumericWrapper): NumericUnknownWrapper {
  return wrapper;
}

export async function stableArray<T>(
  value: readonly T[],
): Promise<readonly T[]> {
  return value;
}

export async function adoptArray<T>(
  value: Promise<readonly T[]>,
): Promise<readonly T[]> {
  return value;
}

export async function stableRecord<T extends StableRecord>(
  value: T,
): Promise<T> {
  return value;
}

export function resolvedArray<T>(value: readonly T[]): Promise<readonly T[]> {
  return Promise.resolve(value);
}
