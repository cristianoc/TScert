// filter compacts a sparse map result through ordinary and guard callbacks.
export function compact(xs: number[]): number[] {
  const mapped = xs.map((value) => {
    xs.pop();
    return value;
  });
  return mapped.filter((value) => value > 0);
}

function isString(value: string | number): value is string {
  return typeof value === "string";
}

export function strings(xs: (string | number)[]): string[] {
  const mapped = xs.map((value) => {
    xs.pop();
    return value;
  });
  return mapped.filter(isString);
}

export function inlineStrings(xs: (string | number)[]): string[] {
  const mapped = xs.map((value) => {
    xs.pop();
    return value;
  });
  return mapped.filter((value): value is string => typeof value === "string");
}
