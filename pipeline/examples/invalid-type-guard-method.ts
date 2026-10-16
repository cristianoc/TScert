// `Box.isWord` answers `true` for numbers, which TypeScript does not check:
// `size(new Box(), 1)` reads `length` off a number, `undefined`, at `number`.
export class Box {
  isWord(x: unknown): x is string {
    return typeof x === "number";
  }
}

export function size(b: Box, v: unknown): number {
  if (b.isWord(v)) return v.length;
  return 0;
}
