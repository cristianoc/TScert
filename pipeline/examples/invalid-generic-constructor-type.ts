// A class constructing a `Box<T>` at every `T` is no constructor of
// `Box<number>` at every `T`: at `T := string` its instance holds a string
// where a number is promised.
class Box<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}

export function wrong(): number {
  // @ts-expect-error
  const make: new <T>(value: T) => Box<number> = Box;
  return new make("text").value;
}
