// The member's declared result does not cover a claim at another element type.
class Pair {
  constructor(private first: number) {}
  pair(second: string): [number, string] {
    return [this.first, second];
  }
}
export function make(): number {
  return new Pair(1).pair("b")[1];
}
