// A unit reading a generic class both as a value at its generic constructor
// type and through a static field: the static read claims the class value at
// an instance, and the module slot holds the instances its reads name, which
// do not meet the scheme the value read needs. Safe in JavaScript, refused
// here: the slot holds the scheme or the instances, not the scheme with the
// static-field facts.
class Box<T> {
  static readonly limit: number = 3;
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}

export function both(): number {
  const make: new <T>(value: T) => Box<T> = Box;
  return Box.limit;
}
