// A class value has construct code only: it meets no generic function type.
class Box<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}

export function asFunction(): void {
  // @ts-expect-error
  const make: <T>(value: T) => Box<T> = Box;
}
