// `{ x }` is `{ x: x }`: the field holds the value the name reads.
export function pack(x: number, y: boolean): { x: number; y: boolean } {
  return { x, y };
}
