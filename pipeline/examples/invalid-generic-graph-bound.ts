// A value within the bound is not a `T`: `{ length: 1 }` is wrong at
// `T := string`, so the meet of `T`'s row and its bound is not below it.
function fabricate<T extends { length: number }>(x: T): T {
  return { length: 1 };
}
