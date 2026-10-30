// A static member of a class declared in a block.
export function counted(): number {
  class Counted {
    static readonly start: number = 1;
  }
  return Counted.start;
}
