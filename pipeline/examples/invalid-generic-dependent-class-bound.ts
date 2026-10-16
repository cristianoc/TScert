// A class's `U extends T` puts `U` below `T`, never `T` below `U`: at
// `T := number`, `U := 1`, the field `second` would hold a number not 1.
class Narrow<T, U extends T> {
  second: U;
  constructor(first: T) {
    this.second = first as U;
  }
}
