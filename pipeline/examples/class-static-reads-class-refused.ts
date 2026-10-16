// A static initializer calling a static method that reads its class runs
// code reading the class value, which JavaScript's code reaches with later
// static fields undefined and the model allocates only after them: outside
// the fragment.
class Counter {
  static readonly base: number = 1;
  static start(): number {
    return Counter.base + 1;
  }
  static readonly first: number = Counter.start();
}

export function use(): number {
  return Counter.first;
}
