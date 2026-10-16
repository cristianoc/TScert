// A default is checked with the constructor's code: this one asserts that an
// optional earlier parameter is present, which an omitted argument is not.
class Pair {
  constructor(
    public first?: number,
    public second: number = first!,
  ) {}
}
export function make(): number {
  return new Pair().second;
}
