// A `typeof` test on a value of a type parameter narrows it to `T & number`,
// which no clause states: the model narrows it to `number`, which is no
// longer read as a `T`.
export function keepNumber<T extends number | string>(x: T): T {
  if (typeof x === "number") {
    return x;
  }
  return x;
}
