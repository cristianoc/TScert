// Parameters with no annotation whose defaults are literals: each states
// the literal's type widened, as TypeScript's `isolatedDeclarations` declares
// it, and the default runs at the call where the argument is `undefined`.
export function flags(singleLine = false, strict = true): boolean {
  return singleLine && strict;
}

export function numbers(
  n = 3,
  negative = -1,
  hex = 0x10,
  big = 10n,
  negativeBig = -1n,
): number {
  return big > negativeBig ? n + negative + hex : 0;
}

export function strings(s = "a", t = `b`): string {
  return s + t;
}

// A written parameter is a cell at the widened type: `true` may replace
// the default `false`.
export function written(singleLine = false, count = 0): number {
  if (!singleLine) singleLine = true;
  count = count + 1;
  return singleLine ? count : 0;
}

export function calls(): number {
  const omitted = flags() ? 1 : 0;
  const undefinedArgument = flags(undefined, false) ? 1 : 0;
  const explicit = flags(true, true) ? 1 : 0;
  return (
    omitted +
    undefinedArgument +
    explicit +
    numbers() +
    numbers(1, 2, 3, 4n, 5n) +
    strings().length +
    written(true)
  );
}

export class Box {
  constructor(
    public width = 1,
    public label = "box",
  ) {}
  grow(by = 2): number {
    return this.width + by;
  }
}

export function boxes(): string {
  const box = new Box();
  const wide = new Box(5, "wide");
  return box.label + wide.label + box.grow() + wide.grow(1);
}

export const arrow = (x: number, factor = 2): number => x * factor;

export const block = (x: number, offset = 1): number => {
  const y = x + offset;
  return y;
};
