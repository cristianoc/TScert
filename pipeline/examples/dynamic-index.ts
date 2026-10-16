// An array read at a key TypeScript types as `number` is the host's
// `%ElementAt%`: an element at an index below the length, else what
// `Array<T>`'s `[n: number]: T` says an own numeric key holds, else
// `undefined`.
function arrayRead(items: number[], index: number): number | undefined {
  return items[index];
}
export function sum(items: readonly number[]): number {
  let total = 0;
  for (let i = 0; i < items.length; i++) {
    const item = items[i];
    if (item !== undefined) total = total + item;
  }
  return total + (arrayRead([1], 0) ?? 0);
}
