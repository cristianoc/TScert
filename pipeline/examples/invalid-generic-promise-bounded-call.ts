export function back<T extends number>(value: Awaited<T>): T {
  return value;
}

export function call(value: number): Promise<number> {
  return back<Promise<number>>(value);
}
