// An overload naming its type parameter otherwise than its implementation
// is refused: the implementation's code is checked at each overload under
// the type parameters they state alike.
export function same<A extends string>(x: A): A;
export function same<B extends string>(x: B): B {
  return x;
}
