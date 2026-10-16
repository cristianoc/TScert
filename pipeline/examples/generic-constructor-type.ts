// A generic constructor type is a scheme of construct signatures: a class
// value meets it when it constructs an instance at every type argument.
class Box<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}

class Pair<T, U> {
  first: T;
  second: U;
  constructor(first: T, second: U) {
    this.first = first;
    this.second = second;
  }
}

class Named {
  constructor(name: string) {}
}

export function boxes(): void {
  const make: new <T>(value: T) => Box<T> = Box;
  const pair: new <T, U>(first: T, second: U) => Pair<T, U> = Pair;
  const named: new (name: string) => Named = Named;
}
