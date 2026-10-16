// Defaults execute under every instantiation, including when no call supplies
// the position. The body can return a rigid value after initialized ground slots.
function genericDefaultResult(seed: boolean): boolean {
  const pick = <T>(
    value: T,
    first: boolean = true,
    second: boolean = first,
  ): T => value;
  return pick(seed);
}

function genericDefaultCallback(seed: boolean): boolean {
  const pick =
    <T>(value: T, flag: boolean = true): (() => T) =>
    (): T =>
      value;
  const read: () => boolean = pick(seed, undefined);
  return read();
}

function genericDefaultValue(seed: boolean): boolean {
  const pick = <T>(value: T, flag: boolean = true): boolean => flag;
  return pick(seed, false);
}
