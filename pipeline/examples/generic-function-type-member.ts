// A method returning a generic function type: the result is a scheme, whose
// signatures take any receiver. Two declarations stating the same scheme
// meet each other.
interface Twice {
  twice(): <A>(x: A) => [A, A];
}

interface Pairs {
  twice(): <A>(x: A) => [A, A];
}

export function pass(t: Pairs): Twice {
  return t;
}
