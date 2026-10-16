// A source type parameter ranges over JavaScript-valued types.
export function sameParameter<T>(left: T, right: T): boolean {
  return left === right;
}
