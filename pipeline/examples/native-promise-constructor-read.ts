export function constructorValue(p: Promise<number>): unknown {
  return p.constructor;
}

export function recordConstructor(
  record: { constructor: number },
  replacement: number,
): number {
  record.constructor = replacement;
  return record.constructor;
}

export function freshRecord(p: Promise<number>): unknown {
  return {};
}
