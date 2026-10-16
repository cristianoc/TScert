export async function queryMixedAwaitedLiteralBroadLength(
  seed: number,
  pick: boolean,
  pending: Promise<number>,
): Promise<number> {
  const items = [seed];
  const view = await (pick ? items : pending);
  if (typeof view === "number") return view;
  items.push(seed);
  return view.length;
}

export async function arrayLength(items: readonly number[]): Promise<number> {
  const value = await items;
  return value.length;
}

export async function recordValue(item: {
  readonly then?: undefined;
  readonly value: number;
}): Promise<number> {
  const value = await item;
  return value.value;
}
