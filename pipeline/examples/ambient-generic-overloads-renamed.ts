// Generic overloads naming their type parameters differently are refused:
// overloads are read as one generic declaration over the type parameters
// every overload states alike.
declare function same<A extends string>(x: A): A;
declare function same<B extends number>(x: B): B;
export function text(): string {
  return same("a");
}
