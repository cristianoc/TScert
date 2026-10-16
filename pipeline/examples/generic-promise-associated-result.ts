export function accept<T>(value: Awaited<T>): Awaited<T> {
  return value;
}

type Cell<T> = { value: Awaited<T> };

export function exchange<T>(cell: Cell<T>, value: Awaited<T>): Awaited<T> {
  const previous = cell.value;
  cell.value = value;
  return previous;
}

export function numeric(value: number): number {
  return accept<number>(value);
}

export function repeated<T>(value: Awaited<T>): Awaited<T> {
  return accept<Awaited<T>>(value);
}

export function nativeResult<T>(value: Awaited<T>): Awaited<T> {
  return accept<Promise<Awaited<T>>>(value);
}
