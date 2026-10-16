// `#x in o` asks whether `o` itself holds the private slot its class's
// construction installs; the model's key test walks the prototype chain,
// and would find an instance's slot from an object inheriting from it.
class Box {
  #value: number = 1;
  static has(o: object): boolean {
    return #value in o;
  }
}

export function make(): Box {
  return new Box();
}
