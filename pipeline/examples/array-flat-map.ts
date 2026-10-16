// `flatMap` with a callback returning an array: the present elements of
// each returned array, in order, in a fresh array.
export function words(lines: readonly string[]): string[] {
  return lines.flatMap((line: string): string[] => line.split(" "));
}

export function pairs(xs: number[]): { at: number; value: number }[] {
  return xs.flatMap((value: number, at: number) =>
    value > 0 ? [{ at, value }] : [],
  );
}

export function nested(xs: readonly number[][]): number[] {
  const flat = xs.flatMap((row: readonly number[]): readonly number[] => row);
  flat.push(0);
  return flat;
}
