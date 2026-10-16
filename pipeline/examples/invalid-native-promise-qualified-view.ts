type StableRecord = { readonly tag: number; readonly then?: number };

async function stableRecord<T extends StableRecord>(value: T): Promise<T> {
  return value;
}

export function unstableView(value: { readonly tag: number }): Promise<{
  readonly tag: number;
}> {
  return stableRecord(value);
}
