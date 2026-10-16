function initializedDefaults(seed: boolean): boolean | undefined {
  const pick = (
    first: boolean | undefined = undefined,
    second?: boolean,
    third: boolean | undefined = second,
  ): boolean | undefined => third;
  return pick(undefined, seed);
}

function defaultEffects(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const pick = (
    first: boolean = (cell.value = false),
    second: boolean = cell.value,
    read: () => boolean = (): boolean => second,
  ): boolean => read();
  return pick();
}

function suppliedDefaultSkipsEffect(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const pick = (first: boolean = (cell.value = false)): boolean => cell.value;
  return pick(true);
}

function nonTrailingDefault(seed: boolean): boolean {
  const pick = (first: boolean = true, second: boolean): boolean =>
    first ? second : false;
  return pick(undefined, seed);
}
