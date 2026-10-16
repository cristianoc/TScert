// A static field is a mutable data property of the class value, whatever
// `readonly` says to TypeScript: code that receives the class value at a
// generic constructor type may write it, so a later read of the field finds
// the written value, not its initializer's. The test supplies `change` as
// `function change(k) { k.limit = 9; }`.
class Box<T> {
  static readonly limit: number = 3;
}
declare function change(k: new <T>() => Box<T>): void;

export function run(): 3 {
  change(Box);
  return Box.limit;
}
