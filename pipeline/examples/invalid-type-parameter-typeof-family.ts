// Where the test fails, the value is still any `T`: no `number`.
export function notNumber<T extends number | string>(x: T): number {
  if (typeof x !== "number") {
    return x;
  }
  return 0;
}
