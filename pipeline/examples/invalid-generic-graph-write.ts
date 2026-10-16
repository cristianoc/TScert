// A `Box<T>` holds a `T` at every instantiation: writing a number into it is
// wrong at `T := string`, so no graph derivation exists.
type Box<T> = { value: T };

function wrong<T>(b: Box<T>, n: number): void {
  b.value = n;
}
