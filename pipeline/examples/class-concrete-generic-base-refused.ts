// A concrete heritage argument specializes the inherited constructor and field.

class Box<T> {
  constructor(public value: T) {}
}

class NumBox extends Box<number> {}

export function read(): number {
  return new NumBox(1).value;
}
