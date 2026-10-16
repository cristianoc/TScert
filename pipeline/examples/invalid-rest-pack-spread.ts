// A spread tuple's positions are the call's actuals, each within the pack's
// bound: a string is no number.
declare function count<T extends readonly number[]>(...args: T): number;

export function wrong(pair: [number, string]): number {
  // @ts-expect-error: a string is no number
  return count(...pair);
}
