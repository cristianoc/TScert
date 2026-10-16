export function back<T extends number>(value: Awaited<T>): T {
  return value;
}

export function forward<T extends number>(value: T): Awaited<T> {
  return value;
}

export function widen<T extends number>(value: Awaited<T>): number {
  return value;
}

export function call(value: number): number {
  return back<number>(value);
}
