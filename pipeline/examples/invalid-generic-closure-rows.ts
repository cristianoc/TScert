// A generic closure over `{ value: T }` returning a number: the one call's
// instance, T := number, would meet it, but the code is checked at every T.
export function wrongBox(box: { value: number }): number {
  // @ts-expect-error
  const read = <T>(b: { value: T }, other: { value: number }): T => other.value;
  return read(box, box);
}
