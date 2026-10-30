// A class declared in the block of a generic function: its instance type
// closes over the function's binder.
export function boxed<T>(value: T): T {
  class Box {
    readonly held: T;
    constructor(held: T) {
      this.held = held;
    }
  }
  return new Box(value).held;
}
