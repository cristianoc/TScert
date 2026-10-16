// A read at a `number` key may be past the end, or at a key that is no
// index: it may be `undefined`.
function arrayRead(items: number[], index: number): number {
  return items[index] as number;
}
