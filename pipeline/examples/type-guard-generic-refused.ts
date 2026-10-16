// A generic guard: its promise signature is quantified, which the producer
// does not encode.
export function isNumber<T>(x: T | number): x is number {
  return typeof x === "number";
}

export function twice(v: string | number): number {
  return isNumber(v) ? v * 2 : 0;
}
