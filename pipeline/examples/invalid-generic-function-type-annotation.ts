// A function returning a string at every type argument is no identity:
// at `T := number` it returns "label" where a number is promised.
function label<T>(_x: T): string {
  return "label";
}

export function wrong(): number {
  // @ts-expect-error
  const f: <T>(v: T) => T = label;
  return f(1);
}
