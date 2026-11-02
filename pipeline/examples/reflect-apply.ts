export function ordered(seed: boolean): boolean {
  const list: [boolean] = [seed];
  const first = (a: boolean): boolean => a;
  return Reflect.apply(first, (list[0] = !seed), list);
}
export function receiver(owner: { value: string }, list: [string]): string {
  const read = function (this: { value: string }, suffix: string): string {
    return this.value + suffix;
  };
  return Reflect.apply(read, owner, list);
}
export function variable(
  fn: (...xs: (string | undefined)[]) => string,
  list: (string | undefined)[],
): string {
  return Reflect.apply(fn, undefined, list);
}

export function orderAll(): number {
  const log = { value: 0 };
  const list: [number] = [4];
  const first = (n: number): number => log.value * 10 + n;
  return Reflect.apply(
    ((log.value = 1), first),
    ((log.value = log.value * 10 + 2), undefined),
    ((log.value = log.value * 10 + 3), list),
  );
}
