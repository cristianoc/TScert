// One operand known to be a primitive, an object or nullish decides the
// comparison whatever the other operand's value: a value of a type parameter
// or of `unknown`.
export function sameNumber<T>(left: T, right: number): boolean {
  return left === right;
}

export function differentRecord<T>(left: { value: number }, right: T): boolean {
  return left !== right;
}

export function isNil<T>(value: T, nil: null): boolean {
  return value == nil;
}

export function unknownFunction(left: unknown, right: () => void): boolean {
  return left === right;
}
