// `U extends T` makes `U` below `T`, never `T` below `U`: at `T := number`,
// `U := 1`, the body would return a number that is not 1.
function narrow<T, U extends T>(x: T, u: U): U {
  const v: T = u;
  return x as U;
}
