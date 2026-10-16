// A generic class with static fields read as a value meets the generic
// constructor type its construct signatures give: the scheme states its
// construct signatures.
class Box<T> {
  static readonly limit: number = 3;
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}

export function boxes(): void {
  const make: new <T>(value: T) => Box<T> = Box;
}
