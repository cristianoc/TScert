class Pair {
  first: number;
  second: string;
  constructor(first: number, second: string) {
    this.first = first;
    this.second = second;
  }
}
class Box<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}
function replace(xs: [number]): string {
  xs[0] = 2;
  return "changed";
}
function choose(xs: [number]): typeof Pair {
  xs[0] = 1;
  return Pair;
}
export function snapshot(): number {
  const xs: [number] = [0];
  const result = new (choose(xs))(...xs, replace(xs));
  return result.first * 10 + xs[0];
}
export function multiple(): number {
  const first: readonly [number] = [3];
  const second: [string] = ["ok"];
  return new Pair(...first, ...second).first;
}
export function generic(): string {
  const args: [string] = ["ok"];
  return new Box(...args).value;
}
export function explicit(): number {
  const args: [number] = [4];
  return new Box<number>(...args).value;
}
export function empty(): number {
  const args: [] = [];
  return new Pair(...args, 5, "ok").first;
}
