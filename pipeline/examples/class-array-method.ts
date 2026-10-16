// A method building an array, and a call to it: the claimed result is the
// producer's own row for `[number, number]`, which the member's declared
// result covers.
class Pair {
  constructor(private first: number) {}
  pair(second: number): [number, number] {
    return [this.first, second];
  }
}
export function make(): number {
  return new Pair(1).pair(2)[0];
}
