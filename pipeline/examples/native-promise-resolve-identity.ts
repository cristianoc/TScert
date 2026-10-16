type StableRecord = { readonly tag: number; readonly then?: number };
type RecordValue = { n: number };

export function nativeIdentity<A>(value: Promise<A>): Promise<A> {
  return Promise.resolve(value);
}

export function nativeWiden<A>(value: Promise<A>): Promise<unknown> {
  return Promise.resolve(value);
}

export function mixedIdentity(
  value: number | Promise<RecordValue>,
): Promise<number | RecordValue> {
  return Promise.resolve(value);
}

export async function readIdentity(
  value: Promise<RecordValue>,
): Promise<number> {
  const result = Promise.resolve(value);
  const record = await result;
  return record.n;
}

export function freshStable<T extends StableRecord>(value: T): Promise<T> {
  return Promise.resolve(value);
}
